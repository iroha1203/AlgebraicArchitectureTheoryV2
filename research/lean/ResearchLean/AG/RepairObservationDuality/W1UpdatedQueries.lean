import ResearchLean.AG.RepairObservationDuality.W1GeneratedNumericalPlan
import ResearchLean.AG.RelativeRepairComposition.W1SymbolicGeneratedRows

/-!
# G-131 E: one unnotified update query, or none after notification

## Implementation notes

The retained x=0 comes from the old actual input (0,0). The new y is either
unreceived or notified. G-130's actual private section and complete public
rows stay unchanged. The controllers consume these retained/notified values
as known information, while their whole unknown-input kernel and costs are
those already proved by C and the actual finite planner.
-/
namespace AAT.AG.RepairObservationDuality.W1UpdatedQueries
open RelativeRepairComposition W1PhysicalInputs W1NumericalEquation W1ObservationCosts PrimitiveQueries
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4096
attribute [local instance] Classical.propDecidable

/-- The updated original input keeps rx at zero and changes only ry. -/
def updated (y : ZMod 3) : Values := fun j => if j then y else 0

/-- The retained x value is the same old input value, independently of the unreceived new y. -/
theorem retained_same (y : ZMod 3) : known 1 (updated y) = known 1 (0 : Values) := by
  ext j
  cases j <;> simp [known_apply,updated]

/-- The same original generated private section is reused after every physical y update. -/
theorem original_section_same (y : ZMod 3) (j : Bool) :
    W1SymbolicLocalStructure.structuralSection 0 y j = W1SymbolicLocalStructure.structuralSection 0 0 j :=
  W1SymbolicLocalStructure.section_same 0 y j

/-- The entire original public row generator remains the same after every y update. -/
theorem original_rows_same (y : ZMod 3) (j : Bool) :
    HEq (FiniteNative.generatedPublicRows (W1AffineInput.originalTower true 0 y).toTower.localCoefficients
      (W1FiniteCoefficients.bases true 0 y) (W1IndexedCover.regions j) W1Regions.fixedRegion
      (ClosedRegion.privateAlwaysEdges W1IndexedCover.regions W1Regions.fixedRegion W1Regions.candidates j)
      (W1FiniteCoefficients.original_linear true 0 y) W1FiniteCoefficients.enumK W1FiniteCoefficients.enumEdges W1FiniteCoefficients.enumFaces)
      (FiniteNative.generatedPublicRows (W1AffineInput.originalTower true 0 0).toTower.localCoefficients
      (W1FiniteCoefficients.bases true 0 0) (W1IndexedCover.regions j) W1Regions.fixedRegion
      (ClosedRegion.privateAlwaysEdges W1IndexedCover.regions W1Regions.fixedRegion W1Regions.candidates j)
      (W1FiniteCoefficients.original_linear true 0 0) W1FiniteCoefficients.enumK W1FiniteCoefficients.enumEdges W1FiniteCoefficients.enumFaces) :=
  W1SymbolicGeneratedRows.generated_rows_same 0 y j

/-- Without notification of y, the full numerical optimum and its generated actual controller require one additional primitive query. -/
theorem unreceived (p : Permissions) (y : ZMod 3) :
    worst evaluate (values ⁻¹' informationFiber (known 1) (known 1 (0 : Values)))
      (W1GeneratedNumericalPlan.procedure p 1 (known 1 (0 : Values))) = 1 ∧
    optimum evaluate (values ⁻¹' informationFiber (known 1) (known 1 (0 : Values)))
      (fun X out => ValidOutput (differential p) (affineRhs rhsLinear 0) (values X) out) = 1 := by
  have h := W1GeneratedNumericalPlan.optimal p 1 (updated y)
  rw [retained_same] at h
  exact ⟨h.2,h.1 ▸ h.2⟩

/-- Once the new y is notified, every original full numerical correction or definite impossibility is acquired at zero additional cost. -/
theorem notified (p : Permissions) (y : ZMod 3) :
    worst evaluate (values ⁻¹' informationFiber (known 2) (known 2 (updated y)))
      (W1GeneratedNumericalPlan.procedure p 2 (known 2 (updated y))) = 0 ∧
    optimum evaluate (values ⁻¹' informationFiber (known 2) (known 2 (updated y)))
      (fun X out => ValidOutput (differential p) (affineRhs rhsLinear 0) (values X) out) = 0 := by
  have h := W1GeneratedNumericalPlan.optimal p 2 (updated y)
  exact ⟨h.2,h.1 ▸ h.2⟩

end AAT.AG.RepairObservationDuality.W1UpdatedQueries
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.W1UpdatedQueries

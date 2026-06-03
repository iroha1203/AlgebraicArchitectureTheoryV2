import Formal.Arch.AAT.GeneratedFlatness
import Formal.Arch.Signature.Curvature

namespace Formal.Arch
namespace AAT

/-- Equality-distance on generated observation coordinates. -/
def generatedObservationDistance :
    ZeroSeparatingDistance GeneratedObservationCoordinate where
  distance := fun left right => if left = right then 0 else 1
  distance_eq_zero_iff := by
    intro left right
    by_cases hEq : left = right
    · simp [hEq]
    · simp [hEq]

namespace GeneratedArchitectureObject

/-- Total curvature of generated reflexive semantic diagrams is zero. -/
theorem generated_totalCurvature_eq_zero
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation) :
    totalCurvature generatedObservationDistance
      object.generatedSemanticSemantics
      object.generatedSemanticDiagrams = 0 := by
  exact
    (totalCurvature_eq_zero_iff_forall_measured_DiagramCommutes
      generatedObservationDistance).mpr
      object.generatedSemanticFlatWithin

/-- Generated semantic diagrams have no measured numerical curvature obstruction. -/
theorem generated_noMeasuredNumericalCurvatureObstruction
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation) :
    NoMeasuredNumericalCurvatureObstruction generatedObservationDistance
      object.generatedSemanticSemantics
      object.generatedSemanticDiagrams := by
  exact
    (totalCurvature_eq_zero_iff_noMeasuredNumericalCurvatureObstruction
      generatedObservationDistance).mp
      object.generated_totalCurvature_eq_zero

end GeneratedArchitectureObject

end AAT
end Formal.Arch

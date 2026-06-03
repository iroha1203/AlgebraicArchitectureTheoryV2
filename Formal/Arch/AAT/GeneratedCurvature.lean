import Formal.Arch.AAT.GeneratedDistance
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

def generatedAtomShapeCoordinateDistance :
    ZeroSeparatingDistance GeneratedAtomShapeCoordinate where
  distance := GeneratedAtomShapeCoordinate.mismatchCount
  distance_eq_zero_iff := by
    intro left right
    exact GeneratedAtomShapeCoordinate.mismatchCount_eq_zero_iff

namespace GeneratedArchitectureObject

/-- Generated shape-coordinate semantics read the full AtomShape distance coordinate. -/
def generatedAtomShapeCoordinateSemantics
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation) :
    Semantics (GeneratedSemanticExpr object)
      GeneratedAtomShapeCoordinate where
  eval := fun carrier => object.generatedAtomShapeCoordinate carrier

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

/--
Total curvature is also zero when measured with the full generated AtomShape
coordinate distance.
-/
theorem generated_shapeCoordinateTotalCurvature_eq_zero
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation) :
    totalCurvature generatedAtomShapeCoordinateDistance
      object.generatedAtomShapeCoordinateSemantics
      object.generatedSemanticDiagrams = 0 := by
  exact
    (totalCurvature_eq_zero_iff_forall_measured_DiagramCommutes
      generatedAtomShapeCoordinateDistance).mpr
      (by
        intro diagram hMeasured
        rcases List.mem_map.mp hMeasured with ⟨carrier, _hCarrier, hEq⟩
        cases hEq
        rfl)

/--
Generated semantic diagrams have no measured numerical curvature obstruction
under the full AtomShape-coordinate distance.
-/
theorem generated_noMeasuredShapeCoordinateCurvatureObstruction
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation) :
    NoMeasuredNumericalCurvatureObstruction
      generatedAtomShapeCoordinateDistance
      object.generatedAtomShapeCoordinateSemantics
      object.generatedSemanticDiagrams := by
  exact
    (totalCurvature_eq_zero_iff_noMeasuredNumericalCurvatureObstruction
      generatedAtomShapeCoordinateDistance).mp
      object.generated_shapeCoordinateTotalCurvature_eq_zero

end GeneratedArchitectureObject

end AAT
end Formal.Arch

import Formal.Arch.AAT.GeneratedCurvature
import Formal.Arch.AAT.GeneratedRepair

namespace Formal.Arch
namespace AAT

universe u v

/--
Generated synthesis candidate.

The candidate is a generated architecture object with a generated law model and
bounded flatness proof. Solver completeness is not claimed here.
-/
structure GeneratedSynthesisCandidate {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation) where
  lawModel : GeneratedArchitectureLawModel object
  flatWithin :
    ArchitectureFlatWithin object.generatedFlatnessModel
      object.generatedComponentUniverse
  synthesisDoesNotCreateAtomsEvidence :
    system.noToolOutputCreatesAtoms
  synthesisBoundary : Prop

namespace GeneratedSynthesisCandidate

/-- The candidate satisfies generated bounded flatness. -/
theorem candidate_flatWithin
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    (candidate : GeneratedSynthesisCandidate object) :
    ArchitectureFlatWithin object.generatedFlatnessModel
      object.generatedComponentUniverse :=
  candidate.flatWithin

/-- The candidate has zero generated semantic curvature. -/
theorem candidate_totalCurvature_eq_zero
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    (_candidate : GeneratedSynthesisCandidate object) :
    totalCurvature generatedObservationDistance
      object.generatedSemanticSemantics object.generatedSemanticDiagrams = 0 :=
  object.generated_totalCurvature_eq_zero

/-- Generated synthesis does not create atom existence. -/
theorem synthesis_does_not_create_atoms
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    (candidate : GeneratedSynthesisCandidate object) :
    system.noToolOutputCreatesAtoms :=
  candidate.synthesisDoesNotCreateAtomsEvidence

end GeneratedSynthesisCandidate

end AAT
end Formal.Arch

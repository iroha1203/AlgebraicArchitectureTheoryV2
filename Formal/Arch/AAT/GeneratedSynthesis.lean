import Formal.Arch.AAT.GeneratedCurvature
import Formal.Arch.AAT.GeneratedRepair
import Formal.Arch.AAT.Synthesis

namespace Formal.Arch
namespace AAT

universe u v

/--
Generated synthesis candidate.

The candidate is a generated architecture object with a generated law model and
bounded flatness derived from that generated law model. Solver completeness is
not claimed here.
-/
structure GeneratedSynthesisCandidate {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation) where
  lawModel : GeneratedArchitectureLawModel object
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
  candidate.lawModel.generatedArchitectureFlatWithin

theorem candidate_flatWithin_eq_lawModel_generated
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    (candidate : GeneratedSynthesisCandidate object) :
    candidate.candidate_flatWithin =
      candidate.lawModel.generatedArchitectureFlatWithin := by
  rfl

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

/--
Generated synthesis candidates induce the existing pure AAT synthesis soundness
package over the generated AAT core.
-/
def toSynthesisSoundnessPackage
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    (candidate : GeneratedSynthesisCandidate object) :
    SynthesisSoundnessPackage
      candidate.lawModel.generatedAATCore
      (GeneratedSynthesisCandidate object) where
  law := candidate.lawModel.generatedDesignLaw
  requiredMolecule := candidate.lawModel.requiredGeneratedMolecule
  lawOnCore := candidate.lawModel.generated_law_on_core
  requiredMoleculesOnCore := by
    intro molecule hRequired
    exact hRequired
  requiredCircuitsOnCore := by
    intro _molecule _hRequired _hCircuit
    trivial
  lawfulnessBridge := candidate.lawModel.generatedLawfulnessBridge
  candidate := candidate
  candidateNoRequiredObstructionCircuit :=
    candidate.lawModel.generated_noRequiredObstructionCircuit
  synthesisDoesNotCreateAtomsEvidence :=
    candidate.synthesis_does_not_create_atoms
  coverageBoundary := candidate.lawModel.lawModelBoundary
  exactnessBoundary := candidate.lawModel.lawModelBoundary
  synthesisBoundary := candidate.synthesisBoundary
  nonConclusions := True

end GeneratedSynthesisCandidate

end AAT
end Formal.Arch

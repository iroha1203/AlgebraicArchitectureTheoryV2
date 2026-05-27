import Formal.Arch.AtomPureAAT
import Formal.Arch.Examples.AtomCoreAATExamples
import Formal.Arch.Examples.AtomOperationExamples
import Formal.Arch.Examples.AtomRepairExamples
import Formal.Arch.Examples.AtomSynthesisExamples

namespace Formal.Arch.AtomicExamples

def noEdgeAtomAxiomatizedPureTheoremSuite :
    AtomAxiomatizedPureTheoremSuite
      Component Edge Diagram
      AtomRepairState AtomRepairRule
      AtomSynthesisState
      AtomRepairState.withForbiddenEdge
      AtomRepairState.repaired where
  core := noEdgePureAtomAxiomatizedAATCore
  zeroCurvature := noEdgePureAtomZeroCurvatureTheoremPackage
  operation := noEdgePureAtomOperationPackage
  operationSurfaceMatches := rfl
  repair := noBadAtomFiniteRepairPackage
  synthesisSpec := noEdgeAtomSynthesisSpec
  synthesisCandidate := AtomSynthesisState.candidate
  synthesisCandidateAtoms := by
    intro atom hAtom
    exact hAtom
  synthesisCandidateMolecules := by
    intro molecule hMolecule
    exact hMolecule
  synthesisCandidateLaws := by
    intro law hLaw
    exact hLaw
  synthesisCandidateNoRequiredObstructionCircuit := trivial
  noArchitectureSignatureDependency := True
  noArchitectureSignatureDependencyEvidence := trivial
  coverageAssumptions := True
  exactnessAssumptions := True
  suiteBoundary := True
  nonConclusions := True

theorem noEdgePureAtomSuite_independent_of_observation :
    noEdgeAtomAxiomatizedPureTheoremSuite.core.surface.noObservationDependency := by
  exact
    AtomAxiomatizedPureTheoremSuite.independent_of_observation
      noEdgeAtomAxiomatizedPureTheoremSuite

theorem noEdgePureAtomSuite_independent_of_sft :
    noEdgeAtomAxiomatizedPureTheoremSuite.core.surface.noSFTDependency := by
  exact
    AtomAxiomatizedPureTheoremSuite.independent_of_sft
      noEdgeAtomAxiomatizedPureTheoremSuite

theorem noEdgePureAtomSuite_independent_of_architecture_signature :
    noEdgeAtomAxiomatizedPureTheoremSuite.noArchitectureSignatureDependency := by
  exact
    AtomAxiomatizedPureTheoremSuite.independent_of_architecture_signature
      noEdgeAtomAxiomatizedPureTheoremSuite

theorem noEdgePureAtomSuite_operation_surface_matches :
    noEdgeAtomAxiomatizedPureTheoremSuite.operation.surface =
      noEdgeAtomAxiomatizedPureTheoremSuite.core.surface := by
  exact
    AtomAxiomatizedPureTheoremSuite.operation_surface_matches
      noEdgeAtomAxiomatizedPureTheoremSuite

theorem noEdgePureAtomSuite_zeroCurvatureLaw_does_not_create_atoms :
    (noEdgeAtomAxiomatizedPureTheoremSuite.core.lawSeparation
      noBadAtomLaw rfl).lawDoesNotCreateAtoms := by
  exact
    AtomAxiomatizedPureTheoremSuite.zeroCurvature_law_does_not_create_atoms
      noEdgeAtomAxiomatizedPureTheoremSuite

theorem noEdgePureAtomSuite_atomZeroCurvature :
    AtomZeroCurvature noBadAtomLaw allSelectedMolecules := by
  exact
    AtomAxiomatizedPureTheoremSuite.atomZeroCurvature
      noEdgeAtomAxiomatizedPureTheoremSuite

theorem noEdgePureAtomSuite_atomLawful_from_atomZeroCurvature :
    LawfulWithinAtomConfiguration noBadAtomLaw allSelectedMolecules := by
  exact
    AtomAxiomatizedPureTheoremSuite.atomLawful_from_atomZeroCurvature
      noEdgeAtomAxiomatizedPureTheoremSuite

theorem noEdgePureAtomSuite_operation_preservesSurfaceInvariant :
    PreservesInvariant
      (AtomPresentationOperation.source
        (surface := noEdgeAtomAxiomatizedPureTheoremSuite.operation.surface))
      (AtomPresentationOperation.target
        (surface := noEdgeAtomAxiomatizedPureTheoremSuite.operation.surface))
      (AtomPresentationOperation.atomSurfacePresentedHolds
        noEdgeAtomAxiomatizedPureTheoremSuite.operation.surface)
      noEdgeAtomAxiomatizedPureTheoremSuite.operation.operation () := by
  exact
    AtomAxiomatizedPureTheoremSuite.operation_preservesSurfaceInvariant
      noEdgeAtomAxiomatizedPureTheoremSuite

theorem noEdgePureAtomSuite_operation_ops_mem_surfaceInvariant :
    Ops
      (AtomPresentationOperation.source
        (surface := noEdgeAtomAxiomatizedPureTheoremSuite.operation.surface))
      (AtomPresentationOperation.target
        (surface := noEdgeAtomAxiomatizedPureTheoremSuite.operation.surface))
      (AtomPresentationOperation.atomSurfacePresentedHolds
        noEdgeAtomAxiomatizedPureTheoremSuite.operation.surface)
      (fun I : Unit => I = ())
      noEdgeAtomAxiomatizedPureTheoremSuite.operation.operation := by
  exact
    AtomAxiomatizedPureTheoremSuite.operation_ops_mem_surfaceInvariant
      noEdgeAtomAxiomatizedPureTheoremSuite

theorem noEdgePureAtomSuite_repair_target_noRequiredCircuit :
    NoRequiredObstructionCircuit noBadAtomLaw allSelectedMolecules := by
  exact
    AtomAxiomatizedPureTheoremSuite.repair_target_noRequiredObstructionCircuit
      noEdgeAtomAxiomatizedPureTheoremSuite

theorem noEdgePureAtomSuite_repair_target_atomZeroCurvature :
    AtomZeroCurvature noBadAtomLaw allSelectedMolecules := by
  exact
    AtomAxiomatizedPureTheoremSuite.repair_target_atomZeroCurvature
      noEdgeAtomAxiomatizedPureTheoremSuite

theorem noEdgePureAtomSuite_repair_target_atomLawful :
    LawfulWithinAtomConfiguration noBadAtomLaw allSelectedMolecules := by
  exact
    AtomAxiomatizedPureTheoremSuite.repair_target_atomLawful
      noEdgeAtomAxiomatizedPureTheoremSuite

theorem noEdgePureAtomSuite_repair_law_does_not_create_atoms :
    (noEdgeAtomAxiomatizedPureTheoremSuite.core.lawSeparation
      noBadAtomLaw rfl).lawDoesNotCreateAtoms := by
  exact
    AtomAxiomatizedPureTheoremSuite.repair_law_does_not_create_atoms
      noEdgeAtomAxiomatizedPureTheoremSuite

theorem noEdgePureAtomSuite_synthesis_candidate_satisfies :
    ArchitectureSatisfies
      noEdgeAtomAxiomatizedPureTheoremSuite.synthesisPackage.system
      noEdgeAtomAxiomatizedPureTheoremSuite.synthesisCandidate := by
  exact
    AtomAxiomatizedPureTheoremSuite.synthesis_candidate_satisfies
      noEdgeAtomAxiomatizedPureTheoremSuite

theorem noEdgePureAtomSuite_synthesis_candidate_atomZeroCurvature :
    AtomZeroCurvature noBadAtomLaw allSelectedMolecules := by
  exact
    AtomAxiomatizedPureTheoremSuite.synthesis_candidate_atomZeroCurvature
      noEdgeAtomAxiomatizedPureTheoremSuite

theorem noEdgePureAtomSuite_synthesis_candidate_atomLawful :
    LawfulWithinAtomConfiguration noBadAtomLaw allSelectedMolecules := by
  exact
    AtomAxiomatizedPureTheoremSuite.synthesis_candidate_atomLawful
      noEdgeAtomAxiomatizedPureTheoremSuite

theorem noEdgePureAtomSuite_synthesis_law_does_not_create_atoms :
    (noEdgeAtomAxiomatizedPureTheoremSuite.core.lawSeparation
      noBadAtomLaw rfl).lawDoesNotCreateAtoms := by
  exact
    AtomAxiomatizedPureTheoremSuite.synthesis_law_does_not_create_atoms
      noEdgeAtomAxiomatizedPureTheoremSuite

end Formal.Arch.AtomicExamples

import Formal.Arch.AtomAAT
import Formal.Arch.Examples.AtomCoreAATExamples
import Formal.Arch.Examples.AtomOperationExamples
import Formal.Arch.Examples.AtomRepairExamples
import Formal.Arch.Examples.AtomSynthesisExamples

namespace Formal.Arch.AtomicExamples

def noEdgeAtomAxiomatizedTheoremSuite :
    AtomAxiomatizedTheoremSuite
      noEdgeArchitectureLawModel
      Edge Diagram
      AtomRepairState AtomRepairRule
      AtomSynthesisState
      AtomRepairState.withForbiddenEdge
      AtomRepairState.repaired where
  pureCore := noEdgePureAtomAxiomatizedAATCore
  aat := noEdgeAtomAxiomatizedAAT
  pureCoreSurfaceMatches := rfl
  pureCoreLawOnSurface := rfl
  operation := noEdgeAtomPresentationOperation
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
  coverageAssumptions := True
  exactnessAssumptions := True
  suiteBoundary := True
  nonConclusions := True

theorem noEdgeAtomSuite_independent_of_observation :
    noEdgeAtomAxiomatizedTheoremSuite.aat.surface.noObservationDependency := by
  exact
    AtomAxiomatizedTheoremSuite.independent_of_observation
      noEdgeAtomAxiomatizedTheoremSuite

theorem noEdgeAtomSuite_independent_of_sft :
    noEdgeAtomAxiomatizedTheoremSuite.aat.surface.noSFTDependency := by
  exact
    AtomAxiomatizedTheoremSuite.independent_of_sft
      noEdgeAtomAxiomatizedTheoremSuite

theorem noEdgeAtomSuite_independent_of_architecture_signature :
    noEdgeAtomAxiomatizedTheoremSuite.pureCore.noArchitectureSignatureDependency := by
  exact
    AtomAxiomatizedTheoremSuite.independent_of_architecture_signature
      noEdgeAtomAxiomatizedTheoremSuite

theorem noEdgeAtomSuite_zeroCurvatureLaw_does_not_create_atoms :
    (noEdgeAtomAxiomatizedTheoremSuite.pureCore.lawSeparation
      noEdgeAtomAxiomatizedTheoremSuite.aat.zeroCurvature.law
      noEdgeAtomAxiomatizedTheoremSuite.pureCoreLawOnSurface).lawDoesNotCreateAtoms := by
  exact
    AtomAxiomatizedTheoremSuite.zeroCurvature_law_does_not_create_atoms
      noEdgeAtomAxiomatizedTheoremSuite

theorem noEdgeAtomSuite_atomZeroCurvature :
    AtomZeroCurvature
      noEdgeAtomAxiomatizedTheoremSuite.aat.zeroCurvature.law
      noEdgeAtomAxiomatizedTheoremSuite.aat.zeroCurvature.requiredMolecule := by
  exact
    AtomAxiomatizedTheoremSuite.atomZeroCurvature
      noEdgeAtomAxiomatizedTheoremSuite

theorem noEdgeAtomSuite_atomLawful_from_atomZeroCurvature :
    LawfulWithinAtomConfiguration
      noEdgeAtomAxiomatizedTheoremSuite.aat.zeroCurvature.law
      noEdgeAtomAxiomatizedTheoremSuite.aat.zeroCurvature.requiredMolecule := by
  exact
    AtomAxiomatizedTheoremSuite.atomLawful_from_atomZeroCurvature
      noEdgeAtomAxiomatizedTheoremSuite

theorem noEdgeAtomSuite_operation_preservesSurfaceInvariant :
    PreservesInvariant
      (AtomPresentationOperation.source
        (surface := noEdgeAtomAxiomatizedTheoremSuite.aat.surface))
      (AtomPresentationOperation.target
        (surface := noEdgeAtomAxiomatizedTheoremSuite.aat.surface))
      (AtomPresentationOperation.atomSurfacePresentedHolds
        noEdgeAtomAxiomatizedTheoremSuite.aat.surface)
      noEdgeAtomAxiomatizedTheoremSuite.operation () := by
  exact
    AtomAxiomatizedTheoremSuite.operation_preservesSurfaceInvariant
      noEdgeAtomAxiomatizedTheoremSuite

theorem noEdgeAtomSuite_pure_operation_preservesSurfaceInvariant :
    PreservesInvariant
      (AtomPresentationOperation.source
        (surface := noEdgeAtomAxiomatizedTheoremSuite.aat.surface))
      (AtomPresentationOperation.target
        (surface := noEdgeAtomAxiomatizedTheoremSuite.aat.surface))
      (AtomPresentationOperation.atomSurfacePresentedHolds
        noEdgeAtomAxiomatizedTheoremSuite.aat.surface)
      noEdgeAtomAxiomatizedTheoremSuite.operation () := by
  exact
    AtomAxiomatizedTheoremSuite.pure_operation_preservesSurfaceInvariant
      noEdgeAtomAxiomatizedTheoremSuite

theorem noEdgeAtomSuite_repair_architectureLawful :
    ArchitectureSignature.ArchitectureLawful
      noEdgeArchitectureLawModel := by
  exact
    AtomAxiomatizedTheoremSuite.architectureLawful_of_repair
      noEdgeAtomAxiomatizedTheoremSuite

theorem noEdgeAtomSuite_synthesis_candidate_satisfies :
    ArchitectureSatisfies
      noEdgeAtomAxiomatizedTheoremSuite.synthesisPackage.system
      noEdgeAtomAxiomatizedTheoremSuite.synthesisCandidate := by
  exact
    AtomAxiomatizedTheoremSuite.synthesis_candidate_satisfies
      noEdgeAtomAxiomatizedTheoremSuite

theorem noEdgeAtomSuite_synthesis_architectureLawful :
    ArchitectureSignature.ArchitectureLawful
      noEdgeArchitectureLawModel := by
  exact
    AtomAxiomatizedTheoremSuite.architectureLawful_of_synthesis
      noEdgeAtomAxiomatizedTheoremSuite

theorem noEdgeAtomSuite_zeroCurvatureTheoremPackage :
    ArchitectureSignature.ArchitectureZeroCurvatureTheoremPackage
      noEdgeArchitectureLawModel := by
  exact
    AtomAxiomatizedTheoremSuite.zeroCurvatureTheoremPackage
      noEdgeAtomAxiomatizedTheoremSuite

theorem noEdgeAtomSuite_zeroCurvatureTheoremPackage_of_repair :
    ArchitectureSignature.ArchitectureZeroCurvatureTheoremPackage
      noEdgeArchitectureLawModel := by
  exact
    AtomAxiomatizedTheoremSuite.zeroCurvatureTheoremPackage_of_repair
      noEdgeAtomAxiomatizedTheoremSuite

theorem noEdgeAtomSuite_zeroCurvatureTheoremPackage_of_synthesis :
    ArchitectureSignature.ArchitectureZeroCurvatureTheoremPackage
      noEdgeArchitectureLawModel := by
  exact
    AtomAxiomatizedTheoremSuite.zeroCurvatureTheoremPackage_of_synthesis
      noEdgeAtomAxiomatizedTheoremSuite

end Formal.Arch.AtomicExamples

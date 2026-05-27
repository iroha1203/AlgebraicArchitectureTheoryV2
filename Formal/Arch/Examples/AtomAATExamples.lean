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

theorem noEdgeAtomSuite_zeroCurvatureLaw_does_not_change_atom_existence :
    (noEdgeAtomAxiomatizedTheoremSuite.pureCore.lawSeparation
      noEdgeAtomAxiomatizedTheoremSuite.aat.zeroCurvature.law
      noEdgeAtomAxiomatizedTheoremSuite.pureCoreLawOnSurface).lawDoesNotChangeAtomExistence := by
  exact
    AtomAxiomatizedTheoremSuite.zeroCurvature_law_does_not_change_atom_existence
      noEdgeAtomAxiomatizedTheoremSuite

theorem noEdgeAtomSuite_zeroCurvatureLaw_atoms_exist_before_law :
    (noEdgeAtomAxiomatizedTheoremSuite.pureCore.lawSeparation
      noEdgeAtomAxiomatizedTheoremSuite.aat.zeroCurvature.law
      noEdgeAtomAxiomatizedTheoremSuite.pureCoreLawOnSurface).atomsExistBeforeLaw := by
  exact
    AtomAxiomatizedTheoremSuite.zeroCurvature_law_atoms_exist_before_law
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

theorem noEdgeAtomSuite_zeroCurvature_strictLayered :
    StrictLayered noEdgeArchitectureLawModel.G := by
  exact
    AtomAxiomatizedTheoremSuite.zeroCurvature_strictLayered
      noEdgeAtomAxiomatizedTheoremSuite

theorem noEdgeAtomSuite_zeroCurvature_walkAcyclic :
    WalkAcyclic noEdgeArchitectureLawModel.G := by
  exact
    AtomAxiomatizedTheoremSuite.zeroCurvature_walkAcyclic
      noEdgeAtomAxiomatizedTheoremSuite

theorem noEdgeAtomSuite_zeroCurvature_projectionSound :
    ProjectionSound
      noEdgeArchitectureLawModel.G
      noEdgeArchitectureLawModel.π
      noEdgeArchitectureLawModel.GA := by
  exact
    AtomAxiomatizedTheoremSuite.zeroCurvature_projectionSound
      noEdgeAtomAxiomatizedTheoremSuite

theorem noEdgeAtomSuite_zeroCurvature_lspCompatible :
    LSPCompatible
      noEdgeArchitectureLawModel.π
      noEdgeArchitectureLawModel.O := by
  exact
    AtomAxiomatizedTheoremSuite.zeroCurvature_lspCompatible
      noEdgeAtomAxiomatizedTheoremSuite

theorem noEdgeAtomSuite_zeroCurvature_boundaryPolicySound :
    ArchitectureSignature.BoundaryPolicySound
      noEdgeArchitectureLawModel.G
      noEdgeArchitectureLawModel.boundaryAllowed := by
  exact
    AtomAxiomatizedTheoremSuite.zeroCurvature_boundaryPolicySound
      noEdgeAtomAxiomatizedTheoremSuite

theorem noEdgeAtomSuite_zeroCurvature_abstractionPolicySound :
    ArchitectureSignature.AbstractionPolicySound
      noEdgeArchitectureLawModel.G
      noEdgeArchitectureLawModel.abstractionAllowed := by
  exact
    AtomAxiomatizedTheoremSuite.zeroCurvature_abstractionPolicySound
      noEdgeAtomAxiomatizedTheoremSuite

theorem noEdgeAtomSuite_requiredMolecule_supported_on_aat_surface :
    AtomMoleculeSupportedBy
      noEdgeAtomAxiomatizedTheoremSuite.aat.surface.selectedAtomUniverse
      componentMolecule := by
  exact
    AtomAxiomatizedTheoremSuite.requiredMolecule_supportedBy_aat_surface_atoms
      noEdgeAtomAxiomatizedTheoremSuite
      componentMoleculeWitness.supportedBy

theorem noEdgeAtomSuite_requiredMolecule_supported_on_pureCore_surface :
    AtomMoleculeSupportedBy
      noEdgeAtomAxiomatizedTheoremSuite.pureCore.surface.selectedAtomUniverse
      componentMolecule := by
  exact
    AtomAxiomatizedTheoremSuite.requiredMolecule_supportedBy_pureCore_surface_atoms
      noEdgeAtomAxiomatizedTheoremSuite
      componentMoleculeWitness.supportedBy

theorem noEdgeAtomSuite_requiredMolecule_atom_is_primitive :
    PrimitiveArchitectureAtom componentAtom := by
  exact
    AtomAxiomatizedTheoremSuite.requiredMolecule_atom_is_primitive
      noEdgeAtomAxiomatizedTheoremSuite
      componentMoleculeWitness.supportedBy
      (by rfl)

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

theorem noEdgeAtomSuite_pure_repair_independent_of_signature :
    noEdgeAtomAxiomatizedTheoremSuite.pureRepairPackage.noArchitectureSignatureDependency := by
  exact
    AtomAxiomatizedTheoremSuite.pure_repair_independent_of_architecture_signature
      noEdgeAtomAxiomatizedTheoremSuite

theorem noEdgeAtomSuite_pure_repair_target_atomZeroCurvature :
    AtomZeroCurvature
      noEdgeAtomAxiomatizedTheoremSuite.aat.zeroCurvature.law
      noEdgeAtomAxiomatizedTheoremSuite.aat.zeroCurvature.requiredMolecule := by
  exact
    AtomAxiomatizedTheoremSuite.pure_repair_target_atomZeroCurvature
      noEdgeAtomAxiomatizedTheoremSuite

theorem noEdgeAtomSuite_pure_repair_law_does_not_create_atoms :
    (noEdgeAtomAxiomatizedTheoremSuite.pureCore.lawSeparation
      noEdgeAtomAxiomatizedTheoremSuite.aat.zeroCurvature.law
      noEdgeAtomAxiomatizedTheoremSuite.pureCoreLawOnSurface).lawDoesNotCreateAtoms := by
  exact
    AtomAxiomatizedTheoremSuite.pure_repair_law_does_not_create_atoms
      noEdgeAtomAxiomatizedTheoremSuite

theorem noEdgeAtomSuite_pure_repair_law_atoms_exist_before_law :
    (noEdgeAtomAxiomatizedTheoremSuite.pureCore.lawSeparation
      noEdgeAtomAxiomatizedTheoremSuite.aat.zeroCurvature.law
      noEdgeAtomAxiomatizedTheoremSuite.pureCoreLawOnSurface).atomsExistBeforeLaw := by
  exact
    AtomAxiomatizedTheoremSuite.pure_repair_law_atoms_exist_before_law
      noEdgeAtomAxiomatizedTheoremSuite

theorem noEdgeAtomSuite_pure_synthesis_independent_of_signature :
    noEdgeAtomAxiomatizedTheoremSuite.pureSynthesisPackage.noArchitectureSignatureDependency := by
  exact
    AtomAxiomatizedTheoremSuite.pure_synthesis_independent_of_architecture_signature
      noEdgeAtomAxiomatizedTheoremSuite

theorem noEdgeAtomSuite_pure_synthesis_candidate_satisfies :
    ArchitectureSatisfies
      noEdgeAtomAxiomatizedTheoremSuite.pureSynthesisPackage.system
      noEdgeAtomAxiomatizedTheoremSuite.synthesisCandidate := by
  exact
    AtomAxiomatizedTheoremSuite.pure_synthesis_candidate_satisfies
      noEdgeAtomAxiomatizedTheoremSuite

theorem noEdgeAtomSuite_pure_synthesis_candidate_atomZeroCurvature :
    AtomZeroCurvature
      noEdgeAtomAxiomatizedTheoremSuite.aat.zeroCurvature.law
      noEdgeAtomAxiomatizedTheoremSuite.aat.zeroCurvature.requiredMolecule := by
  exact
    AtomAxiomatizedTheoremSuite.pure_synthesis_candidate_atomZeroCurvature
      noEdgeAtomAxiomatizedTheoremSuite

theorem noEdgeAtomSuite_pure_synthesis_law_does_not_create_atoms :
    (noEdgeAtomAxiomatizedTheoremSuite.pureCore.lawSeparation
      noEdgeAtomAxiomatizedTheoremSuite.aat.zeroCurvature.law
      noEdgeAtomAxiomatizedTheoremSuite.pureCoreLawOnSurface).lawDoesNotCreateAtoms := by
  exact
    AtomAxiomatizedTheoremSuite.pure_synthesis_law_does_not_create_atoms
      noEdgeAtomAxiomatizedTheoremSuite

theorem noEdgeAtomSuite_pure_synthesis_law_atoms_exist_before_law :
    (noEdgeAtomAxiomatizedTheoremSuite.pureCore.lawSeparation
      noEdgeAtomAxiomatizedTheoremSuite.aat.zeroCurvature.law
      noEdgeAtomAxiomatizedTheoremSuite.pureCoreLawOnSurface).atomsExistBeforeLaw := by
  exact
    AtomAxiomatizedTheoremSuite.pure_synthesis_law_atoms_exist_before_law
      noEdgeAtomAxiomatizedTheoremSuite

theorem noEdgeAtomSuite_pureTheoremSuite_atomZeroCurvature :
    AtomZeroCurvature noBadAtomLaw allSelectedMolecules := by
  exact
    AtomAxiomatizedPureTheoremSuite.atomZeroCurvature
      noEdgeAtomAxiomatizedTheoremSuite.pureTheoremSuite

theorem noEdgeAtomSuite_pureTheoremSuite_independent_of_signature :
    noEdgeAtomAxiomatizedTheoremSuite.pureTheoremSuite.noArchitectureSignatureDependency := by
  exact
    AtomAxiomatizedPureTheoremSuite.independent_of_architecture_signature
      noEdgeAtomAxiomatizedTheoremSuite.pureTheoremSuite

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

theorem noEdgeAtomSuite_matrixDiagnosticCorollaries :
    ArchitectureSignature.MatrixDiagnosticCorollaries
      noEdgeArchitectureLawModel := by
  exact
    AtomAxiomatizedTheoremSuite.matrixDiagnosticCorollaries
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

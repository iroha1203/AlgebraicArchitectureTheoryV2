import Formal.Arch.Repair.AtomSynthesis
import Formal.Arch.Examples.AtomZeroCurvatureExamples

namespace Formal.Arch.AtomicExamples

inductive AtomSynthesisState where
  | candidate
  deriving DecidableEq, Repr

def noEdgeAtomSynthesisSpec :
    AtomAATSynthesisSpec
      noEdgePureAATSurface
      noBadAtomLaw
      allSelectedMolecules
      AtomSynthesisState where
  stateHasAtom := fun _ atom => noEdgePureAATSurface.atoms atom
  stateHasMolecule := fun _ molecule =>
    noEdgePureAATSurface.molecules molecule
  stateHasLaw := fun _ law => noEdgePureAATSurface.laws law
  stateNoRequiredObstructionCircuit := fun _ => True
  stateNoRequiredObstructionCircuitSound := by
    intro _state _hState molecule _hRequired hCircuit
    exact obstructionCircuit_bad hCircuit
  interpretationBoundary := True
  nonConclusions := True

def noEdgeAtomAxiomatizedSynthesisPackage :
    AtomAxiomatizedSynthesisPackage
      noEdgeArchitectureLawModel Edge Diagram AtomSynthesisState where
  aat := noEdgeAtomAxiomatizedAAT
  spec := noEdgeAtomSynthesisSpec
  candidate := AtomSynthesisState.candidate
  candidateAtoms := by
    intro atom hAtom
    exact hAtom
  candidateMolecules := by
    intro molecule hMolecule
    exact hMolecule
  candidateLaws := by
    intro law hLaw
    exact hLaw
  candidateNoRequiredObstructionCircuit := trivial
  coverageAssumptions := True
  exactnessAssumptions := True
  synthesisBoundary := True
  nonConclusions := True

theorem noEdgeAtomSynthesis_candidate_satisfies :
    ArchitectureSatisfies
      noEdgeAtomAxiomatizedSynthesisPackage.system
      noEdgeAtomAxiomatizedSynthesisPackage.candidate := by
  exact
    AtomAxiomatizedSynthesisPackage.candidate_satisfies
      noEdgeAtomAxiomatizedSynthesisPackage

theorem noEdgeAtomSynthesis_candidate_satisfies_via_package :
    ArchitectureSatisfies
      noEdgeAtomAxiomatizedSynthesisPackage.system
      (AtomAxiomatizedSynthesisPackage.synthesisSoundnessPackage
        noEdgeAtomAxiomatizedSynthesisPackage).candidate := by
  exact
    AtomAxiomatizedSynthesisPackage.candidate_satisfies_via_synthesisPackage
      noEdgeAtomAxiomatizedSynthesisPackage

theorem noEdgeAtomSynthesis_candidate_noRequiredCircuit :
    NoRequiredObstructionCircuit noBadAtomLaw allSelectedMolecules := by
  exact
    AtomAxiomatizedSynthesisPackage.candidate_noRequiredObstructionCircuit
      noEdgeAtomAxiomatizedSynthesisPackage

theorem noEdgeAtomSynthesis_architectureLawful :
    ArchitectureSignature.ArchitectureLawful
      noEdgeArchitectureLawModel := by
  exact
    AtomAxiomatizedSynthesisPackage.architectureLawful_of_synthesis
      noEdgeAtomAxiomatizedSynthesisPackage

theorem noEdgeAtomSynthesis_requiredSignatureAxesZero :
    ArchitectureSignature.RequiredSignatureAxesZero
      (ArchitectureSignature.ArchitectureLawModel.signatureOf
        noEdgeArchitectureLawModel) := by
  exact
    AtomAxiomatizedSynthesisPackage.requiredSignatureAxesZero_of_synthesis
      noEdgeAtomAxiomatizedSynthesisPackage

theorem noEdgeAtomSynthesis_zeroCurvatureTheoremPackage :
    ArchitectureSignature.ArchitectureZeroCurvatureTheoremPackage
      noEdgeArchitectureLawModel := by
  exact
    AtomAxiomatizedSynthesisPackage.architectureZeroCurvatureTheoremPackage_of_synthesis
      noEdgeAtomAxiomatizedSynthesisPackage

inductive AtomNoSolutionState where
  | candidate
  deriving DecidableEq, Repr

inductive AtomNoSolutionConstraint where
  | requiresRelationAtom
  | forbidsRelationAtom
  deriving DecidableEq, Repr

def noSolutionStateHasAtom
    (_state : AtomNoSolutionState)
    (atom : ArchitectureAtom Component Edge Diagram) : Prop :=
  atom = relationAtom

def relationAtomContradictorySystem :
    SynthesisConstraintSystem
      AtomNoSolutionState AtomNoSolutionConstraint where
  required := fun _ => True
  satisfies := fun state constraint =>
    match constraint with
    | AtomNoSolutionConstraint.requiresRelationAtom =>
        noSolutionStateHasAtom state relationAtom
    | AtomNoSolutionConstraint.forbidsRelationAtom =>
        ¬ noSolutionStateHasAtom state relationAtom

def relationAtomConstraintContradiction :
    AtomConstraintContradiction
      relationAtomContradictorySystem
      noSolutionStateHasAtom where
  atom := relationAtom
  requiresAtom := AtomNoSolutionConstraint.requiresRelationAtom
  forbidsAtom := AtomNoSolutionConstraint.forbidsRelationAtom
  requiresAtomRequired := trivial
  forbidsAtomRequired := trivial
  requiresAtomSound := by
    intro state hRequires
    exact hRequires
  forbidsAtomSound := by
    intro state hForbids
    exact hForbids
  contradictionBoundary := True
  nonConclusions := True

inductive RelationAtomNoSolutionCertificate where
  | contradiction
  deriving DecidableEq, Repr

def relationAtomNoSolutionCertificate :
    NoSolutionCertificate
      RelationAtomNoSolutionCertificate
      relationAtomContradictorySystem
      RelationAtomNoSolutionCertificate.contradiction :=
  relationAtomConstraintContradiction.noSolutionCertificate
    RelationAtomNoSolutionCertificate
    RelationAtomNoSolutionCertificate.contradiction

theorem relationAtomContradiction_noArchitecture :
    NoArchitectureSatisfies relationAtomContradictorySystem := by
  exact relationAtomConstraintContradiction.noArchitectureSatisfies

theorem relationAtomContradiction_valid_certificate :
    ValidNoSolutionCertificate relationAtomNoSolutionCertificate := by
  trivial

theorem relationAtomNoSolution_from_valid_certificate :
    NoArchitectureSatisfies relationAtomContradictorySystem := by
  exact
    NoSolutionCertificate.sound_of_valid
      relationAtomNoSolutionCertificate
      relationAtomContradiction_valid_certificate

end Formal.Arch.AtomicExamples

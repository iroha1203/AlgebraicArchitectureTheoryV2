import Formal.Arch.AtomCoreAAT
import Formal.Arch.Examples.AtomicExamples

namespace Formal.Arch.AtomicExamples

/-- Law-separation witness for the finite forbidden-edge pure Atom-AAT core. -/
def pureAtomCoreLawSeparation
    (law : DesignLaw Component Edge Diagram)
    (_hLaw : pureAATSurface.laws law) :
    AtomLawSeparation Component Edge Diagram where
  law := law
  selectedMolecule := pureAATSurface.molecules
  atomsExistBeforeLaw := True
  atomsExistBeforeLawEvidence := trivial
  lawDoesNotCreateAtoms := True
  lawDoesNotCreateAtomsEvidence := trivial
  lawDoesNotChangeAtomExistence := True
  lawDoesNotChangeAtomExistenceEvidence := trivial
  nonConclusions := True

/--
The forbidden-edge example read as pure Atom-axiomatized AAT, before any
ArchitectureSignature or ArchSig observation layer is attached.
-/
def pureAtomAxiomatizedAATCore :
    AtomAxiomatizedPureAAT Component Edge Diagram where
  surface := pureAATSurface
  lawSeparation := pureAtomCoreLawSeparation
  lawSeparationMatches := by
    intro law hLaw
    rfl
  lawEvaluatesSurfaceMolecules := by
    intro law hLaw molecule hMolecule
    exact hMolecule
  circuitClosure := by
    intro law molecule hLaw hMolecule hCircuit
    exact ⟨hLaw, hMolecule, hCircuit⟩
  noArchitectureSignatureDependency := True
  noArchitectureSignatureDependencyEvidence := trivial
  atomAxiomBoundary := True
  moleculeAxiomBoundary := True
  lawAxiomBoundary := True
  circuitAxiomBoundary := True
  pureTheoryBoundary := True
  nonConclusions := True

theorem pureAtomCore_independent_of_observation :
    pureAtomAxiomatizedAATCore.surface.noObservationDependency := by
  exact
    AtomAxiomatizedPureAAT.independent_of_observation
      pureAtomAxiomatizedAATCore

theorem pureAtomCore_independent_of_sft :
    pureAtomAxiomatizedAATCore.surface.noSFTDependency := by
  exact
    AtomAxiomatizedPureAAT.independent_of_sft
      pureAtomAxiomatizedAATCore

theorem pureAtomCore_independent_of_architecture_signature :
    pureAtomAxiomatizedAATCore.noArchitectureSignatureDependency := by
  exact
    AtomAxiomatizedPureAAT.independent_of_architecture_signature
      pureAtomAxiomatizedAATCore

theorem pureAtomCore_forbiddenLaw_does_not_create_atoms :
    (pureAtomAxiomatizedAATCore.lawSeparation forbiddenEdgeLaw rfl).lawDoesNotCreateAtoms := by
  exact
    AtomAxiomatizedPureAAT.selected_law_does_not_create_atoms
      pureAtomAxiomatizedAATCore rfl

theorem pureAtomCore_forbiddenCircuit_on_surface :
    pureAtomAxiomatizedAATCore.surface.circuits
      (law := forbiddenEdgeLaw)
      (molecule := forbiddenEdgeMolecule)
      rfl
      (Or.inl rfl)
      singletonForbiddenMolecule_obstruction := by
  exact
    AtomAxiomatizedPureAAT.circuit_on_surface
      pureAtomAxiomatizedAATCore rfl (Or.inl rfl)
      singletonForbiddenMolecule_obstruction

def noBadAtomLawfulnessBridge :
    AtomLawfulnessBridge noBadAtomLaw allSelectedMolecules where
  badWitnessComplete := by
    intro M _hRequired hBad
    exact False.elim hBad
  circuitBad := by
    intro M _hRequired hCircuit
    exact obstructionCircuit_bad hCircuit
  coverageBoundary := True
  exactnessBoundary := True
  nonConclusions := True

theorem noBadNoRequiredObstructionCircuit :
    NoRequiredObstructionCircuit noBadAtomLaw allSelectedMolecules := by
  intro M _hRequired hCircuit
  exact obstructionCircuit_bad hCircuit

def noEdgePureAATSurface : AATPureTheorySurface Component Edge Diagram where
  atoms := selectedAtomUniverse.selectedAtom
  molecules := allSelectedMolecules
  laws := fun law => law = noBadAtomLaw
  circuits := fun {law} {molecule} _hLaw _hMolecule _hCircuit =>
    law = noBadAtomLaw ∧ allSelectedMolecules molecule ∧
      ObstructionCircuit law molecule
  atomCoreBoundary := True
  moleculeBoundary := True
  lawBoundary := True
  patternInterpretationBoundary := True
  noObservationDependency := True
  noObservationDependencyEvidence := trivial
  noSFTDependency := True
  noSFTDependencyEvidence := trivial
  nonConclusions := True

/-- Law-separation witness for the no-edge pure Atom-AAT core. -/
def noEdgePureAtomCoreLawSeparation
    (law : DesignLaw Component Edge Diagram)
    (_hLaw : noEdgePureAATSurface.laws law) :
    AtomLawSeparation Component Edge Diagram where
  law := law
  selectedMolecule := noEdgePureAATSurface.molecules
  atomsExistBeforeLaw := True
  atomsExistBeforeLawEvidence := trivial
  lawDoesNotCreateAtoms := True
  lawDoesNotCreateAtomsEvidence := trivial
  lawDoesNotChangeAtomExistence := True
  lawDoesNotChangeAtomExistenceEvidence := trivial
  nonConclusions := True

/--
The no-edge zero-curvature example read as pure Atom-axiomatized AAT, before
the existing Signature-level theorem package is consumed.
-/
def noEdgePureAtomAxiomatizedAATCore :
    AtomAxiomatizedPureAAT Component Edge Diagram where
  surface := noEdgePureAATSurface
  lawSeparation := noEdgePureAtomCoreLawSeparation
  lawSeparationMatches := by
    intro law hLaw
    rfl
  lawEvaluatesSurfaceMolecules := by
    intro law hLaw molecule hMolecule
    exact hMolecule
  circuitClosure := by
    intro law molecule hLaw hMolecule hCircuit
    exact ⟨hLaw, hMolecule, hCircuit⟩
  noArchitectureSignatureDependency := True
  noArchitectureSignatureDependencyEvidence := trivial
  atomAxiomBoundary := True
  moleculeAxiomBoundary := True
  lawAxiomBoundary := True
  circuitAxiomBoundary := True
  pureTheoryBoundary := True
  nonConclusions := True

theorem noEdgePureAtomCore_independent_of_observation :
    noEdgePureAtomAxiomatizedAATCore.surface.noObservationDependency := by
  exact
    AtomAxiomatizedPureAAT.independent_of_observation
      noEdgePureAtomAxiomatizedAATCore

theorem noEdgePureAtomCore_independent_of_sft :
    noEdgePureAtomAxiomatizedAATCore.surface.noSFTDependency := by
  exact
    AtomAxiomatizedPureAAT.independent_of_sft
      noEdgePureAtomAxiomatizedAATCore

theorem noEdgePureAtomCore_independent_of_architecture_signature :
    noEdgePureAtomAxiomatizedAATCore.noArchitectureSignatureDependency := by
  exact
    AtomAxiomatizedPureAAT.independent_of_architecture_signature
      noEdgePureAtomAxiomatizedAATCore

theorem noEdgePureAtomCore_noBadLaw_does_not_create_atoms :
    (noEdgePureAtomAxiomatizedAATCore.lawSeparation noBadAtomLaw rfl).lawDoesNotCreateAtoms := by
  exact
    AtomAxiomatizedPureAAT.selected_law_does_not_create_atoms
      noEdgePureAtomAxiomatizedAATCore rfl

def noEdgePureAtomZeroCurvatureTheoremPackage :
    AtomZeroCurvatureTheoremPackage noEdgePureAtomAxiomatizedAATCore where
  law := noBadAtomLaw
  requiredMolecule := allSelectedMolecules
  lawOnSurface := rfl
  requiredMoleculesOnSurface := by
    intro molecule _hRequired
    trivial
  requiredCircuitsOnSurface := by
    intro molecule hRequired hCircuit
    exact ⟨rfl, hRequired, hCircuit⟩
  lawfulnessBridge := noBadAtomLawfulnessBridge
  atomZeroCurvature := noBadNoRequiredObstructionCircuit
  atomZeroCurvatureBoundary := True
  theoremPackageBoundary := True
  nonConclusions := True

theorem noEdgePureAtomZeroCurvature :
    AtomZeroCurvature noBadAtomLaw allSelectedMolecules := by
  exact noEdgePureAtomZeroCurvatureTheoremPackage.atomZeroCurvature

theorem noEdgePureAtomZeroCurvature_atomLawful :
    LawfulWithinAtomConfiguration noBadAtomLaw allSelectedMolecules := by
  exact
    AtomZeroCurvatureTheoremPackage.atomLawful
      noEdgePureAtomZeroCurvatureTheoremPackage

theorem noEdgePureAtomZeroCurvature_law_does_not_create_atoms :
    (noEdgePureAtomAxiomatizedAATCore.lawSeparation noBadAtomLaw rfl).lawDoesNotCreateAtoms := by
  exact
    AtomZeroCurvatureTheoremPackage.law_does_not_create_atoms
      noEdgePureAtomZeroCurvatureTheoremPackage

end Formal.Arch.AtomicExamples

import Formal.Arch.Signature.AtomZeroCurvature
import Formal.Arch.Examples.AtomicExamples

namespace Formal.Arch.AtomicExamples

/-- Finite component universe used by the atom-derived zero-curvature example. -/
def allComponents : List Component :=
  [Component.api, Component.database]

theorem allComponents_nodup : allComponents.Nodup := by
  simp [allComponents]

theorem allComponents_covers (component : Component) :
    component ∈ allComponents := by
  cases component <;> simp [allComponents]

def noEdgeComponentUniverse : ComponentUniverse noEdgeGraph :=
  ComponentUniverse.full noEdgeGraph allComponents allComponents_nodup
    allComponents_covers

def noEdgeArchitectureLawModel :
    ArchitectureSignature.ArchitectureLawModel Component Component Unit where
  G := noEdgeGraph
  π := identityProjection
  GA := noEdgeGraph
  O := observationToUnit
  U := noEdgeComponentUniverse
  boundaryAllowed := fun _ _ => True
  abstractionAllowed := fun _ _ => True
  lspPairClosed := by
    intro x y _hSame
    exact ⟨allComponents_covers x, allComponents_covers y⟩

instance instDecidableRelNoEdgeArchitectureLawModelG :
    DecidableRel noEdgeArchitectureLawModel.G.edge := by
  intro src dst
  exact isFalse (by
    intro hEdge
    exact hEdge)

instance instDecidableRelNoEdgeArchitectureLawModelGA :
    DecidableRel noEdgeArchitectureLawModel.GA.edge := by
  intro src dst
  exact isFalse (by
    intro hEdge
    exact hEdge)

instance instDecidableRelNoEdgeArchitectureLawModelBoundaryAllowed :
    DecidableRel noEdgeArchitectureLawModel.boundaryAllowed := by
  intro src dst
  exact isTrue trivial

instance instDecidableRelNoEdgeArchitectureLawModelAbstractionAllowed :
    DecidableRel noEdgeArchitectureLawModel.abstractionAllowed := by
  intro src dst
  exact isTrue trivial

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

def noEdgeAtomDerivedZeroCurvaturePackage :
    ArchitectureSignature.AtomDerivedZeroCurvaturePackage
      noEdgeArchitectureLawModel Edge Diagram where
  law := noBadAtomLaw
  requiredMolecule := allSelectedMolecules
  lawfulnessBridge := noBadAtomLawfulnessBridge
  noRequiredObstructionCircuit := noBadNoRequiredObstructionCircuit
  layering := noEdgeLayeringAtomArrangement
  projection := identityProjectionAtomArrangement
  lspCompatibleFromLawful := by
    intro _hLawful x y _hSame
    rfl
  boundaryPolicySoundFromLawful := by
    intro _hLawful _c _d _hEdge
    trivial
  abstractionPolicySoundFromLawful := by
    intro _hLawful _c _d _hEdge
    trivial
  atomBoundary := True
  moleculeBoundary := True
  obstructionCircuitBoundary := True
  zeroCurvatureBoundary := True
  nonConclusions := True

theorem noEdgeAtomDerived_architectureLawful :
    ArchitectureSignature.ArchitectureLawful noEdgeArchitectureLawModel := by
  exact
    ArchitectureSignature.AtomDerivedZeroCurvaturePackage.architectureLawful
      noEdgeAtomDerivedZeroCurvaturePackage

theorem noEdgeAtomDerived_requiredSignatureAxesZero :
    ArchitectureSignature.RequiredSignatureAxesZero
      (ArchitectureSignature.ArchitectureLawModel.signatureOf
        noEdgeArchitectureLawModel) := by
  exact
    ArchitectureSignature.AtomDerivedZeroCurvaturePackage.requiredSignatureAxesZero
      noEdgeAtomDerivedZeroCurvaturePackage

theorem noEdgeAtomDerived_zeroCurvatureTheoremPackage :
    ArchitectureSignature.ArchitectureZeroCurvatureTheoremPackage
      noEdgeArchitectureLawModel := by
  exact
    ArchitectureSignature.AtomDerivedZeroCurvaturePackage.architectureZeroCurvatureTheoremPackage
      noEdgeAtomDerivedZeroCurvaturePackage

end Formal.Arch.AtomicExamples

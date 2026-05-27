import Formal.Arch.Signature.AtomZeroCurvature
import Formal.Arch.Examples.AtomCoreAATExamples

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

def noEdgeStaticAtomArrangementPackage :
    ArchitectureSignature.StaticAtomArrangementLawPackage
      noEdgeArchitectureLawModel noBadAtomLaw allSelectedMolecules where
  layering := noEdgeLayeringAtomArrangement
  projection := identityProjectionAtomArrangement
  lsp := identityLSPAtomArrangement
  boundaryPolicy := allowAllBoundaryPolicyAtomArrangement
  abstractionPolicy := allowAllAbstractionPolicyAtomArrangement
  arrangementBoundary := True
  nonConclusions := True

theorem noEdgeStaticAtomArrangementPackage_architectureLawful :
    ArchitectureSignature.ArchitectureLawful noEdgeArchitectureLawModel := by
  exact
    noEdgeStaticAtomArrangementPackage.architectureLawful_of_lawful
      noBadAtomLaw_lawful

def noEdgeAtomDerivedZeroCurvaturePackage :
    ArchitectureSignature.AtomDerivedZeroCurvaturePackage
      noEdgeArchitectureLawModel Edge Diagram :=
  ArchitectureSignature.AtomDerivedZeroCurvaturePackage.ofStaticAtomArrangementPackage
      (X := noEdgeArchitectureLawModel)
      noEdgePureAtomZeroCurvatureTheoremPackage
      noEdgeStaticAtomArrangementPackage
      True True True True True

theorem noEdgeAtomDerived_from_pure_atom_zero_curvature :
    ArchitectureSignature.ArchitectureZeroCurvatureTheoremPackage
      noEdgeArchitectureLawModel := by
  exact
    ArchitectureSignature.AtomDerivedZeroCurvaturePackage.architectureZeroCurvatureTheoremPackage_of_atomZeroCurvatureTheoremPackage
      (X := noEdgeArchitectureLawModel)
      noEdgePureAtomZeroCurvatureTheoremPackage
      noEdgeLayeringAtomArrangement
      identityProjectionAtomArrangement
      (by
        intro _hLawful x y _hSame
        rfl)
      (by
        intro _hLawful _c _d _hEdge
        trivial)
      (by
        intro _hLawful _c _d _hEdge
        trivial)

theorem noEdgeAtomDerived_from_full_atom_arrangements :
    ArchitectureSignature.ArchitectureZeroCurvatureTheoremPackage
      noEdgeArchitectureLawModel := by
  exact
    ArchitectureSignature.AtomDerivedZeroCurvaturePackage.architectureZeroCurvatureTheoremPackage_of_staticAtomArrangementPackage
      (X := noEdgeArchitectureLawModel)
      noEdgePureAtomZeroCurvatureTheoremPackage
      noEdgeStaticAtomArrangementPackage

def noEdgeAtomAxiomatizedAAT :
    ArchitectureSignature.AtomAxiomatizedAAT
      noEdgeArchitectureLawModel Edge Diagram :=
  ArchitectureSignature.AtomAxiomatizedAAT.ofPureAtomStaticArrangementPackage
    (X := noEdgeArchitectureLawModel)
    noEdgePureAtomZeroCurvatureTheoremPackage
    noEdgeStaticAtomArrangementPackage
    True True True

theorem noEdgeAtomAxiomatized_independent_of_observation :
    noEdgeAtomAxiomatizedAAT.surface.noObservationDependency := by
  exact
    ArchitectureSignature.AtomAxiomatizedAAT.independent_of_observation
      noEdgeAtomAxiomatizedAAT

theorem noEdgeAtomAxiomatized_independent_of_sft :
    noEdgeAtomAxiomatizedAAT.surface.noSFTDependency := by
  exact
    ArchitectureSignature.AtomAxiomatizedAAT.independent_of_sft
      noEdgeAtomAxiomatizedAAT

theorem noEdgeAtomDerived_atomZeroCurvature :
    AtomZeroCurvature noBadAtomLaw allSelectedMolecules := by
  exact
    ArchitectureSignature.AtomDerivedZeroCurvaturePackage.atomZeroCurvature
      noEdgeAtomDerivedZeroCurvaturePackage

theorem noEdgeAtomAxiomatized_atomZeroCurvature :
    AtomZeroCurvature
      noEdgeAtomAxiomatizedAAT.zeroCurvature.law
      noEdgeAtomAxiomatizedAAT.zeroCurvature.requiredMolecule := by
  exact
    ArchitectureSignature.AtomAxiomatizedAAT.atomZeroCurvature
      noEdgeAtomAxiomatizedAAT

theorem noEdgeAtomAxiomatized_strictLayered :
    StrictLayered noEdgeGraph := by
  exact
    ArchitectureSignature.AtomAxiomatizedAAT.strictLayered
      noEdgeAtomAxiomatizedAAT

theorem noEdgeAtomAxiomatized_projectionSound :
    ProjectionSound noEdgeGraph identityProjection noEdgeGraph := by
  exact
    ArchitectureSignature.AtomAxiomatizedAAT.projectionSound
      noEdgeAtomAxiomatizedAAT

theorem noEdgeAtomAxiomatized_lspCompatible :
    LSPCompatible identityProjection observationToUnit := by
  exact
    ArchitectureSignature.AtomAxiomatizedAAT.lspCompatible
      noEdgeAtomAxiomatizedAAT

theorem noEdgeAtomDerived_architectureLawful :
    ArchitectureSignature.ArchitectureLawful noEdgeArchitectureLawModel := by
  exact
    ArchitectureSignature.AtomDerivedZeroCurvaturePackage.architectureLawful
      noEdgeAtomDerivedZeroCurvaturePackage

theorem noEdgeAtomDerived_strictLayered :
    StrictLayered noEdgeGraph := by
  exact
    ArchitectureSignature.AtomDerivedZeroCurvaturePackage.strictLayered
      noEdgeAtomDerivedZeroCurvaturePackage

theorem noEdgeAtomDerived_walkAcyclic :
    WalkAcyclic noEdgeGraph := by
  exact
    ArchitectureSignature.AtomDerivedZeroCurvaturePackage.walkAcyclic
      noEdgeAtomDerivedZeroCurvaturePackage

theorem noEdgeAtomDerived_projectionSound :
    ProjectionSound noEdgeGraph identityProjection noEdgeGraph := by
  exact
    ArchitectureSignature.AtomDerivedZeroCurvaturePackage.projectionSound
      noEdgeAtomDerivedZeroCurvaturePackage

theorem noEdgeAtomDerived_noProjectionObstruction :
    NoProjectionObstruction noEdgeGraph identityProjection noEdgeGraph := by
  exact
    ArchitectureSignature.AtomDerivedZeroCurvaturePackage.noProjectionObstruction
      noEdgeAtomDerivedZeroCurvaturePackage

theorem noEdgeAtomDerived_lspCompatible :
    LSPCompatible identityProjection observationToUnit := by
  exact
    ArchitectureSignature.AtomDerivedZeroCurvaturePackage.lspCompatible
      noEdgeAtomDerivedZeroCurvaturePackage

theorem noEdgeAtomDerived_boundaryPolicySound :
    ArchitectureSignature.BoundaryPolicySound noEdgeGraph (fun _ _ => True) := by
  exact
    ArchitectureSignature.AtomDerivedZeroCurvaturePackage.boundaryPolicySound
      noEdgeAtomDerivedZeroCurvaturePackage

theorem noEdgeAtomDerived_abstractionPolicySound :
    ArchitectureSignature.AbstractionPolicySound noEdgeGraph (fun _ _ => True) := by
  exact
    ArchitectureSignature.AtomDerivedZeroCurvaturePackage.abstractionPolicySound
      noEdgeAtomDerivedZeroCurvaturePackage

theorem noEdgeAtomDerived_matrixDiagnosticCorollaries :
    ArchitectureSignature.MatrixDiagnosticCorollaries
      noEdgeArchitectureLawModel := by
  exact
    ArchitectureSignature.AtomDerivedZeroCurvaturePackage.matrixDiagnosticCorollaries
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

theorem noEdgeAtomAxiomatized_zeroCurvatureTheoremPackage :
    ArchitectureSignature.ArchitectureZeroCurvatureTheoremPackage
      noEdgeArchitectureLawModel := by
  exact
    ArchitectureSignature.AtomAxiomatizedAAT.architectureZeroCurvatureTheoremPackage
      noEdgeAtomAxiomatizedAAT

theorem noEdgeAtomAxiomatized_matrixDiagnosticCorollaries :
    ArchitectureSignature.MatrixDiagnosticCorollaries
      noEdgeArchitectureLawModel := by
  exact
    ArchitectureSignature.AtomAxiomatizedAAT.matrixDiagnosticCorollaries
      noEdgeAtomAxiomatizedAAT

end Formal.Arch.AtomicExamples

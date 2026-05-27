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

def noEdgeAtomDerivedZeroCurvaturePackage :
    ArchitectureSignature.AtomDerivedZeroCurvaturePackage
      noEdgeArchitectureLawModel Edge Diagram :=
  ArchitectureSignature.AtomDerivedZeroCurvaturePackage.ofAtomZeroCurvatureTheoremPackage
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

def noEdgeAtomAxiomatizedAAT :
    ArchitectureSignature.AtomAxiomatizedAAT
      noEdgeArchitectureLawModel Edge Diagram :=
  ArchitectureSignature.AtomAxiomatizedAAT.ofPureAtomZeroCurvature
    (X := noEdgeArchitectureLawModel)
    noEdgePureAtomZeroCurvatureTheoremPackage
    noEdgeLayeringAtomArrangement
    identityProjectionAtomArrangement
    (by
      intro _hLawful x y _hSame
      rfl
    )
    (by
      intro _hLawful _c _d _hEdge
      trivial
    )
    (by
      intro _hLawful _c _d _hEdge
      trivial
    )
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

theorem noEdgeAtomAxiomatized_zeroCurvatureTheoremPackage :
    ArchitectureSignature.ArchitectureZeroCurvatureTheoremPackage
      noEdgeArchitectureLawModel := by
  exact
    ArchitectureSignature.AtomAxiomatizedAAT.architectureZeroCurvatureTheoremPackage
      noEdgeAtomAxiomatizedAAT

end Formal.Arch.AtomicExamples

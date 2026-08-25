import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticNaturalIsoTransport

/-!
# Split natural-isomorphism squares on diagnostic data

The four sides remain visible: a source alignment followed by component
comparison is identified with an outer comparison followed by a target
alignment.  The output records value and morphism equations, rather than an
equality of proof terms or two unrelated forward conclusions.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

/-- Diagnostic consequences of a commutative square of core-fiber natural
isomorphisms. -/
structure FiberwiseDiagnosticNaturalIsoSquareCompatibility
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (data : FiberwiseAdmissibleTransportData G U X)
    {outerDirect componentDirect outerVia componentVia :
      CoreFiber X ⥤ CoreFiber Y}
    (sourceAlignment : outerDirect ≅ componentDirect)
    (componentComparison : componentDirect ≅ componentVia)
    (outerComparison : outerDirect ≅ outerVia)
    (targetAlignment : outerVia ≅ componentVia) : Prop where
  /-- The two comparison paths agree pointwise on every diagnostic package. -/
  packagePath_eq : ∀ vertex,
    (sourceAlignment.app (data.package vertex)) ≪≫
        (componentComparison.app (data.package vertex)) =
      (outerComparison.app (data.package vertex)) ≪≫
        (targetAlignment.app (data.package vertex))
  /-- Arbitrary target reselections transported around either side of the
  square agree. -/
  reselectionPath_eq : ∀ reselection,
    transportEdgeReselectionAlongNaturalIso data componentComparison
        (transportEdgeReselectionAlongNaturalIso data sourceAlignment
          reselection) =
      transportEdgeReselectionAlongNaturalIso data targetAlignment
        (transportEdgeReselectionAlongNaturalIso data outerComparison
          reselection)
  /-- The two successive endpoint conjugations of the generated comparator
  agree as values. -/
  comparatorPath_eq : ∀ cell,
    packageFiberAutMulEquivOfCoreFiberIso
        (componentComparison.app (data.package (G.twoTarget cell)))
        (packageFiberAutMulEquivOfCoreFiberIso
          (sourceAlignment.app (data.package (G.twoTarget cell)))
          ((data.map outerDirect).comparator cell)) =
      packageFiberAutMulEquivOfCoreFiberIso
        (targetAlignment.app (data.package (G.twoTarget cell)))
        (packageFiberAutMulEquivOfCoreFiberIso
          (outerComparison.app (data.package (G.twoTarget cell)))
          ((data.map outerDirect).comparator cell))
  /-- The complete reselected path commutes through the exposed two-step
  component route. -/
  reselectedPath_componentRoute : ∀ reselection {i j}
      (path : G.Path i j),
    fiberReselectedPath (data.map outerDirect) reselection path ≫
        (sourceAlignment.app (data.package j)).hom ≫
        (componentComparison.app (data.package j)).hom =
      (sourceAlignment.app (data.package i)).hom ≫
        (componentComparison.app (data.package i)).hom ≫
        fiberReselectedPath (data.map componentVia)
          (transportEdgeReselectionAlongNaturalIso data componentComparison
            (transportEdgeReselectionAlongNaturalIso data sourceAlignment
              reselection)) path
  /-- Coherence is the same proposition at the common endpoint reached by the
  exposed component route. -/
  coherentAt_componentRoute_iff : ∀ reselection,
    CoherentAt (data.transported outerDirect) reselection ↔
      CoherentAt (data.transported componentVia)
        (transportEdgeReselectionAlongNaturalIso data componentComparison
          (transportEdgeReselectionAlongNaturalIso data sourceAlignment
            reselection))
  /-- Vanishing is invariant between the common endpoints of the square. -/
  vanishing_endpoint_iff :
    TransportObstructionVanishes (data.transported outerDirect) ↔
      TransportObstructionVanishes (data.transported componentVia)

/-- Construct the diagnostic square from an equality of the two generated
natural-isomorphism paths. -/
noncomputable def fiberwiseDiagnosticNaturalIsoSquareCompatibility
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (data : FiberwiseAdmissibleTransportData G U X)
    {outerDirect componentDirect outerVia componentVia :
      CoreFiber X ⥤ CoreFiber Y}
    (sourceAlignment : outerDirect ≅ componentDirect)
    (componentComparison : componentDirect ≅ componentVia)
    (outerComparison : outerDirect ≅ outerVia)
    (targetAlignment : outerVia ≅ componentVia)
    (square : sourceAlignment ≪≫ componentComparison =
      outerComparison ≪≫ targetAlignment) :
    FiberwiseDiagnosticNaturalIsoSquareCompatibility data sourceAlignment
      componentComparison outerComparison targetAlignment where
  packagePath_eq vertex := congrArg
    (fun comparison => comparison.app (data.package vertex)) square
  reselectionPath_eq reselection := by
    rw [← transportEdgeReselectionAlongNaturalIso_trans,
      ← transportEdgeReselectionAlongNaturalIso_trans, square]
  comparatorPath_eq cell := by
    have hpoint :
        (sourceAlignment.app (data.package (G.twoTarget cell))) ≪≫
            (componentComparison.app (data.package (G.twoTarget cell))) =
          (outerComparison.app (data.package (G.twoTarget cell))) ≪≫
            (targetAlignment.app (data.package (G.twoTarget cell))) :=
      congrArg
        (fun comparison => comparison.app (data.package (G.twoTarget cell)))
        square
    rw [← packageFiberAutMulEquivOfCoreFiberIso_trans,
      ← packageFiberAutMulEquivOfCoreFiberIso_trans, hpoint]
  reselectedPath_componentRoute := by
    intro reselection i j path
    have naturality := fiberReselectedPath_naturality_iso data
      (sourceAlignment ≪≫ componentComparison) reselection path
    rw [transportEdgeReselectionAlongNaturalIso_trans] at naturality
    simpa only [Iso.trans_hom, NatTrans.comp_app, Category.assoc] using naturality
  coherentAt_componentRoute_iff reselection := by
    have compatibility := coherentAt_naturalIso_iff data
      (sourceAlignment ≪≫ componentComparison) reselection
    rw [transportEdgeReselectionAlongNaturalIso_trans] at compatibility
    exact compatibility
  vanishing_endpoint_iff :=
    transportObstructionVanishes_naturalIso_iff data
      (sourceAlignment ≪≫ componentComparison)

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct

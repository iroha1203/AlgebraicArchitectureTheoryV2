import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleRawCochainImages
import ResearchLean.AG.CrossStageCoherence.Unification

/-!
# Pseudofunctor coherence on compatible finite routes

The literal empty source path is identified with the canonical identity lift
through the genuine geometry-fiber unitor.  For each two-cell, the genuine
pseudofunctor-compositor normalization on both generated routes is then
identified with the Cartesian pullback of the corresponding source
normalization.  Thus the finite route coherence is not inferred merely from
group map laws or recursive path evaluation.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 3000000

namespace UpperGeometryCompatibleProblemInputData

/-- The genuine geometry-fiber unitor normalizes the canonical identity lift
to the literal empty path in the authored source transport. -/
theorem compatibleSourceRoutePathNil_unitor
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (i : P.Vertex) :
    geomFiberLift
          (𝟙 (packagePoint (input.sourceGeometry i).package.core))
          (geomFiberMk (input.sourceGeometry i).package) ≫
        (geomFiberUnitorApp
          (packagePoint (input.sourceGeometry i).package.core)
          (geomFiberMk (input.sourceGeometry i).package)).hom.1 =
      input.compatibleSourceRouteData.lift.pathLift (.nil i) := by
  simpa only [TwoLayerLiftData.pathLift] using
    geomFiberUnitorApp_hom_fac
      (packagePoint (input.sourceGeometry i).package.core)
      (geomFiberMk (input.sourceGeometry i).package)

/-- The package projection of the same unitor normalization is the literal
empty-path package identity. -/
theorem compatibleSourceRoutePathNil_unitor_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (i : P.Vertex) :
    (geomFiberLift
          (𝟙 (packagePoint (input.sourceGeometry i).package.core))
          (geomFiberMk (input.sourceGeometry i).package)).base.comp
        (geomFiberUnitorApp
          (packagePoint (input.sourceGeometry i).package.core)
          (geomFiberMk (input.sourceGeometry i).package)).hom.1.base =
      (input.compatibleSourceRouteData.lift.pathLift (.nil i)).base := by
  exact congrArg GeometryTotalHom.base
    (input.compatibleSourceRoutePathNil_unitor i)

/-- The genuine unitor normalization on a generated base endpoint is exactly
the pulled-back source group identity. -/
theorem generatedBaseRouteUnitor_eq_pullback_one
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (i : P.Vertex) :
    geomFiberLift
          (𝟙 (packagePoint (input.generatedBaseRouteGeometryAt i).core))
          (geomFiberMk (input.generatedBaseRouteGeometryAt i)) ≫
        (geomFiberUnitorApp
          (packagePoint (input.generatedBaseRouteGeometryAt i).core)
          (geomFiberMk (input.generatedBaseRouteGeometryAt i))).hom.1 =
      CompositeFiberAut.hom
        (input.generatedBaseCompositeFiberAutAt i
          (1 : CompositeFiberAut (input.sourceGeometry i).package)) := by
  rw [geomFiberUnitorApp_hom_fac,
    input.generatedBaseCompositeFiberAutAt_one]
  rfl

/-- The pulled generated endpoint has the independent unitor/map-one
normalization. -/
theorem generatedPulledRouteUnitor_eq_pullback_one
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (i : P.Vertex) :
    geomFiberLift
          (𝟙 (packagePoint (input.generatedPulledRouteGeometryAt i).core))
          (geomFiberMk (input.generatedPulledRouteGeometryAt i)) ≫
        (geomFiberUnitorApp
          (packagePoint (input.generatedPulledRouteGeometryAt i).core)
          (geomFiberMk (input.generatedPulledRouteGeometryAt i))).hom.1 =
      CompositeFiberAut.hom
        (input.generatedPulledCompositeFiberAutAt i
          (1 : CompositeFiberAut (input.sourceGeometry i).package)) := by
  rw [geomFiberUnitorApp_hom_fac,
    input.generatedPulledCompositeFiberAutAt_one]
  rfl

/-- Base-route compatibility between the genuine generated and source
unitors, through the route-specific empty-path factorization. -/
theorem generatedBaseRouteUnitor_compatibility
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (i : P.Vertex) :
    RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (geomFiberLift
                (𝟙 (packagePoint (input.generatedBaseRouteGeometryAt i).core))
                (geomFiberMk (input.generatedBaseRouteGeometryAt i)) ≫
              (geomFiberUnitorApp
                (packagePoint (input.generatedBaseRouteGeometryAt i).core)
                (geomFiberMk (input.generatedBaseRouteGeometryAt i))).hom.1))
        (input.generatedBaseRouteLegAt i) =
      RefinementGeometryHom.comp (input.generatedBaseRouteLegAt i)
        ((exactGeometryToRefinementGeometry U).map
          (geomFiberLift
                (𝟙 (packagePoint (input.sourceGeometry i).package.core))
                (geomFiberMk (input.sourceGeometry i).package) ≫
              (geomFiberUnitorApp
                (packagePoint (input.sourceGeometry i).package.core)
                (geomFiberMk (input.sourceGeometry i).package)).hom.1)) := by
  rw [geomFiberUnitorApp_hom_fac,
    input.compatibleSourceRoutePathNil_unitor]
  exact input.generatedBaseRoutePath_nil_fac i

/-- Pulled-route compatibility between the two genuine unitor normalizations. -/
theorem generatedPulledRouteUnitor_compatibility
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (i : P.Vertex) :
    RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (geomFiberLift
                (𝟙 (packagePoint (input.generatedPulledRouteGeometryAt i).core))
                (geomFiberMk (input.generatedPulledRouteGeometryAt i)) ≫
              (geomFiberUnitorApp
                (packagePoint (input.generatedPulledRouteGeometryAt i).core)
                (geomFiberMk (input.generatedPulledRouteGeometryAt i))).hom.1))
        (input.generatedPulledRouteLegAt i) =
      RefinementGeometryHom.comp (input.generatedPulledRouteLegAt i)
        ((exactGeometryToRefinementGeometry U).map
          (geomFiberLift
                (𝟙 (packagePoint (input.sourceGeometry i).package.core))
                (geomFiberMk (input.sourceGeometry i).package) ≫
              (geomFiberUnitorApp
                (packagePoint (input.sourceGeometry i).package.core)
                (geomFiberMk (input.sourceGeometry i).package)).hom.1)) := by
  rw [geomFiberUnitorApp_hom_fac,
    input.compatibleSourceRoutePathNil_unitor]
  exact input.generatedPulledRoutePath_nil_fac i

/-- Package-level projection of base-route unitor compatibility. -/
theorem generatedBaseRouteUnitor_compatibility_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (i : P.Vertex) :
    (RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (geomFiberLift
                (𝟙 (packagePoint (input.generatedBaseRouteGeometryAt i).core))
                (geomFiberMk (input.generatedBaseRouteGeometryAt i)) ≫
              (geomFiberUnitorApp
                (packagePoint (input.generatedBaseRouteGeometryAt i).core)
                (geomFiberMk (input.generatedBaseRouteGeometryAt i))).hom.1))
        (input.generatedBaseRouteLegAt i)).base =
      (RefinementGeometryHom.comp (input.generatedBaseRouteLegAt i)
        ((exactGeometryToRefinementGeometry U).map
          (geomFiberLift
                (𝟙 (packagePoint (input.sourceGeometry i).package.core))
                (geomFiberMk (input.sourceGeometry i).package) ≫
              (geomFiberUnitorApp
                (packagePoint (input.sourceGeometry i).package.core)
                (geomFiberMk (input.sourceGeometry i).package)).hom.1))).base := by
  exact congrArg RefinementGeometryHom.base
    (input.generatedBaseRouteUnitor_compatibility i)

/-- Package-level projection of pulled-route unitor compatibility. -/
theorem generatedPulledRouteUnitor_compatibility_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (i : P.Vertex) :
    (RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (geomFiberLift
                (𝟙 (packagePoint (input.generatedPulledRouteGeometryAt i).core))
                (geomFiberMk (input.generatedPulledRouteGeometryAt i)) ≫
              (geomFiberUnitorApp
                (packagePoint (input.generatedPulledRouteGeometryAt i).core)
                (geomFiberMk (input.generatedPulledRouteGeometryAt i))).hom.1))
        (input.generatedPulledRouteLegAt i)).base =
      (RefinementGeometryHom.comp (input.generatedPulledRouteLegAt i)
        ((exactGeometryToRefinementGeometry U).map
          (geomFiberLift
                (𝟙 (packagePoint (input.sourceGeometry i).package.core))
                (geomFiberMk (input.sourceGeometry i).package) ≫
              (geomFiberUnitorApp
                (packagePoint (input.sourceGeometry i).package.core)
                (geomFiberMk (input.sourceGeometry i).package)).hom.1))).base := by
  exact congrArg RefinementGeometryHom.base
    (input.generatedPulledRouteUnitor_compatibility i)

/-- The generated base-route pseudofunctor compositor normalization is the
Cartesian pullback of the source normalization. -/
theorem generatedBaseRoutePseudofunctorComparator_eq_pullback
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    pseudofunctorCanonicalComparator input.generatedBaseRouteData 1 cell =
      input.generatedBaseCompositeFiberAutAt (P.twoTarget cell)
        (pseudofunctorCanonicalComparator
          input.compatibleSourceRouteData 1 cell) := by
  rw [pseudofunctorCanonicalComparator_eq_upper,
    input.generatedBaseRouteCanonicalComparator_eq_pullback,
    pseudofunctorCanonicalComparator_eq_upper]

/-- The pulled route satisfies the independently generated compositor
normalization compatibility. -/
theorem generatedPulledRoutePseudofunctorComparator_eq_pullback
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    pseudofunctorCanonicalComparator input.generatedPulledRouteData 1 cell =
      input.generatedPulledCompositeFiberAutAt (P.twoTarget cell)
        (pseudofunctorCanonicalComparator
          input.compatibleSourceRouteData 1 cell) := by
  rw [pseudofunctorCanonicalComparator_eq_upper,
    input.generatedPulledRouteCanonicalComparator_eq_pullback,
    pseudofunctorCanonicalComparator_eq_upper]

end UpperGeometryCompatibleProblemInputData

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct

import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryRouteContextCancellation

/-!
# Direct canonical-authored route geometry homs

The realization-exact route equivalences normalize the authored source
geometry directly.  This module equips that normalization with the actual
base and pulled lax route bases, using the theorem-generated realization
supplies and composite context cancellation rather than new input fields.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 3000000

private theorem contextObjectExt
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A}
    {W V : Site.ContextCategoryObject C} (h : W.ctx = V.ctx) : W = V := by
  cases W
  cases V
  cases h
  rfl

/-- The complete geometry contract carried by an upper-pair pullback whose
forward upper map is the literal upper map of an actual lax base. -/
noncomputable def upperPairPullRefinementGeomReadHom
    {U : AtomCarrier.{u}} {P : AATCorePackage U}
    (G : GeometryPackage.{u, v} U)
    (f : RefinementPackageHom ⟨P⟩ ⟨G.core⟩)
    (backward : SignedExactCoreReadingHom G.core P)
    (hcancel : backward.comp f.upper = SignedExactCoreReadingHom.refl G.core)
    (S : UpperRealizationTransportSupply P G.core f.upper)
    (hctx : ∀ W : G.site.category,
      (refinementGeometryContextForward
        (G := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
          G f.upper backward) (H := G) f
        (refinementGeometryContextBackward
          (G := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
            G f.upper backward) (H := G) f W)).ctx = W.ctx) :
    RefinementGeomReadHom
      (UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
        G f.upper backward) G f where
  coverage := {
    requiredSupport := fun _ h => h
    requiredEquationCoordinate := fun _ h => h
    selectedViolationWitness := fun _ h => h
    requiredAxis := fun _ h => h
    supportVisibleOn := fun _ _ h => h
    equationCoordinateVisibleOn := fun _ _ h => h
    violationWitnessVisibleOn := fun _ _ h => h
    axisReadableOn := fun _ _ h => h
    boundaryVisibleOn := fun _ _ h => h
  }
  overlap := {
    overlapIso := fun base left right => by
      apply eqToIso
      apply contextObjectExt
      change
        (refinementGeometryContextForward
          (G := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
            G f.upper backward) (H := G) f
          (refinementGeometryContextBackward
            (G := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
              G f.upper backward) (H := G) f
            ⟨G.geometry.overlap.overlap
              (refinementGeometryContextForward
                (G := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
                  G f.upper backward) (H := G) f
                (refinementGeometryContextBackward
                  (G := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
                    G f.upper backward) (H := G) f ⟨base⟩)).ctx
              (refinementGeometryContextForward
                (G := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
                  G f.upper backward) (H := G) f
                (refinementGeometryContextBackward
                  (G := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
                    G f.upper backward) (H := G) f ⟨left⟩)).ctx
              (refinementGeometryContextForward
                (G := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
                  G f.upper backward) (H := G) f
                (refinementGeometryContextBackward
                  (G := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
                    G f.upper backward) (H := G) f ⟨right⟩)).ctx⟩)).ctx =
          G.geometry.overlap.overlap base left right
      rw [hctx ⟨base⟩, hctx ⟨left⟩, hctx ⟨right⟩]
      exact hctx _
  }
  coefficientHom := RingHom.id G.Coefficient
  raw_eq := by
    change G.raw = UpperGeometryCleavage.rawReindexUpper
      (UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
        G f.upper backward).geometry G.geometry f.upper
      ((UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
        G f.upper backward).raw.baseChange (RingHom.id G.Coefficient))
    have hid :
        (UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
          G f.upper backward).raw.baseChange (RingHom.id G.Coefficient) =
          (UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
            G f.upper backward).raw :=
      LawAlgebra.RawAmbientRestrictionSystem.baseChange_id _
    rw [hid]
    exact (UpperGeometryCleavage.rawReindexUpper_cancel
      (UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
        G f.upper backward).geometry G.geometry f.upper backward hcancel G.raw).symm
  supportComp := S.supportComp
  axisComp := S.axisComp
  observableComp := S.observableComp
  supportReads := S.supportReads
  axisReads := S.axisReads
  observableReads := S.observableReads
  support_naturality := S.support_naturality
  axis_naturality := S.axis_naturality
  observable_naturality := S.observable_naturality

/-- The corresponding total refinement-geometry hom. -/
noncomputable def upperPairPullRefinementGeometryHom
    {U : AtomCarrier.{u}} {P : AATCorePackage U}
    (G : GeometryPackage.{u, v} U)
    (f : RefinementPackageHom ⟨P⟩ ⟨G.core⟩)
    (backward : SignedExactCoreReadingHom G.core P)
    (hcancel : backward.comp f.upper = SignedExactCoreReadingHom.refl G.core)
    (S : UpperRealizationTransportSupply P G.core f.upper)
    (hctx : ∀ W : G.site.category,
      (refinementGeometryContextForward
        (G := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
          G f.upper backward) (H := G) f
        (refinementGeometryContextBackward
          (G := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
            G f.upper backward) (H := G) f W)).ctx = W.ctx) :
    RefinementGeometryHom
      (UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
        G f.upper backward) G where
  base := f
  geometry := upperPairPullRefinementGeomReadHom G f backward hcancel S hctx

namespace UpperGeometryCompatibleProblemInputData

/-- Direct base-route hom from the canonical-authored normalization to the
authored source geometry, with the literal generated lax lower route. -/
noncomputable def canonicalAuthoredBaseRouteGeometryHomAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    RefinementGeometryHom (input.canonicalAuthoredBaseRouteGeometryAt i)
      (input.sourceGeometry i).package :=
  upperPairPullRefinementGeometryHom
    (input.sourceGeometry i).package
    (input.generatedBaseRouteLegAt i).base
    (input.generatedBaseRouteUpperEquivalenceAt i).backward
    (input.generatedBaseRouteUpperEquivalenceAt i).backward_forward
    (input.canonicalAuthoredBaseRouteForwardSupplyAt i)
    (input.canonicalAuthoredBaseRouteContextForward_backwardAt i)

@[simp] theorem canonicalAuthoredBaseRouteGeometryHomAt_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredBaseRouteGeometryHomAt i).base =
      (input.generatedBaseRouteLegAt i).base :=
  rfl

@[simp] theorem canonicalAuthoredBaseRouteGeometryHomAt_coefficientHom
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredBaseRouteGeometryHomAt i).geometry.coefficientHom =
      RingHom.id k :=
  rfl

/-- Direct pulled-route hom from its independent canonical-authored
normalization to the authored source geometry. -/
noncomputable def canonicalAuthoredPulledRouteGeometryHomAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    RefinementGeometryHom (input.canonicalAuthoredPulledRouteGeometryAt i)
      (input.sourceGeometry i).package :=
  upperPairPullRefinementGeometryHom
    (input.sourceGeometry i).package
    (input.generatedPulledRouteLegAt i).base
    (input.generatedPulledRouteUpperEquivalenceAt i).backward
    (input.generatedPulledRouteUpperEquivalenceAt i).backward_forward
    (input.canonicalAuthoredPulledRouteForwardSupplyAt i)
    (input.canonicalAuthoredPulledRouteContextForward_backwardAt i)

@[simp] theorem canonicalAuthoredPulledRouteGeometryHomAt_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredPulledRouteGeometryHomAt i).base =
      (input.generatedPulledRouteLegAt i).base :=
  rfl

@[simp] theorem canonicalAuthoredPulledRouteGeometryHomAt_coefficientHom
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredPulledRouteGeometryHomAt i).geometry.coefficientHom =
      RingHom.id k :=
  rfl

end UpperGeometryCompatibleProblemInputData

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct

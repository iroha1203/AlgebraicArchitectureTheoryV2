import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryRealizationFactorNaturality

/-!
# Universal geometry factors for realization-exact upper normalizations

An arbitrary complete geometry hom whose base factors through an upper-pair
normalization has a canonical complete factor.  The coverage and raw data are
inherited from the composite, overlap is pulled back along the actual lax
base, and the three realization carriers are returned by the reviewed
inverse-at-forward maps.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 3000000

private theorem signed_comp_assoc
    {U : AtomCarrier.{u}} {P Q R S : AATCorePackage U}
    (a : SignedExactCoreReadingHom P Q)
    (b : SignedExactCoreReadingHom Q R)
    (c : SignedExactCoreReadingHom R S) :
    (a.comp b).comp c = a.comp (b.comp c) := by
  apply SignedExactCoreReadingHom.ext <;> rfl

private theorem signed_comp_refl
    {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    (a : SignedExactCoreReadingHom P Q) :
    a.comp (SignedExactCoreReadingHom.refl Q) = a := by
  apply SignedExactCoreReadingHom.ext <;> rfl

private theorem contextObjectExt
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A}
    {W V : Site.ContextCategoryObject C} (h : W.ctx = V.ctx) : W = V := by
  cases W
  cases V
  cases h
  rfl

/-- Package a lax refinement's complete upper map with an authored inverse. -/
def refinementExactUpperEquivalence
    {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    (f : RefinementPackageHom ⟨P⟩ ⟨Q⟩)
    (backward : SignedExactCoreReadingHom Q P)
    (forward_backward : f.upper.comp backward =
      SignedExactCoreReadingHom.refl P)
    (backward_forward : backward.comp f.upper =
      SignedExactCoreReadingHom.refl Q) : ExactUpperEquivalence P Q where
  forward := f.upper
  backward := backward
  forward_backward := forward_backward
  backward_forward := backward_forward

/-- Raw backward-after-forward context cancellation follows from the supplied
forward-after-backward equality and the authored inverse equivalence. -/
private theorem refinementContextBackward_forward_ctx
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (f : RefinementPackageHom ⟨G.core⟩ ⟨H.core⟩)
    (backward : SignedExactCoreReadingHom H.core G.core)
    (forward_backward : f.upper.comp backward =
      SignedExactCoreReadingHom.refl G.core)
    (backward_forward : backward.comp f.upper =
      SignedExactCoreReadingHom.refl H.core)
    (hctx : ∀ V : H.site.category,
      (refinementGeometryContextForward f
        (refinementGeometryContextBackward f V)).ctx = V.ctx)
    (W : G.site.category) :
    (refinementGeometryContextBackward f
      (refinementGeometryContextForward f W)).ctx = W.ctx := by
  let e := refinementExactUpperEquivalence f backward
    forward_backward backward_forward
  have h := congrArg
    (fun X : Site.ArchCtx H.core.object =>
      ((upperCoreContextFunctor e.backward).obj ⟨X⟩).ctx)
    (hctx (refinementGeometryContextForward f W))
  change
    ((upperCoreContextFunctor e.backward).obj
      ((upperCoreContextFunctor e.forward).obj
        (refinementGeometryContextBackward f
          (refinementGeometryContextForward f W)))).ctx =
      ((upperCoreContextFunctor e.backward).obj
        ((upperCoreContextFunctor e.forward).obj W)).ctx at h
  simpa only [e.forwardBackwardContext] using h

/-- Backward transport of a composite through its final forward context
recovers the preceding factor context. -/
private theorem refinementCompositeContextBackward_forward_ctx
    {U : AtomCarrier.{u}} {G H K : GeometryPackage.{u, v} U}
    (f : RefinementPackageHom ⟨G.core⟩ ⟨H.core⟩)
    (backward : SignedExactCoreReadingHom H.core G.core)
    (forward_backward : f.upper.comp backward =
      SignedExactCoreReadingHom.refl G.core)
    (backward_forward : backward.comp f.upper =
      SignedExactCoreReadingHom.refl H.core)
    (hctx : ∀ V : H.site.category,
      (refinementGeometryContextForward f
        (refinementGeometryContextBackward f V)).ctx = V.ctx)
    (g : RefinementPackageHom ⟨K.core⟩ ⟨G.core⟩) (W : G.site.category) :
    refinementGeometryContextBackwardMap (g.comp f)
        (refinementGeometryContextForward f W).ctx =
      (refinementGeometryContextBackward g W).ctx := by
  change (refinementGeometryContextBackward g
    (refinementGeometryContextBackward f
      (refinementGeometryContextForward f W))).ctx = _
  rw [contextObjectExt (refinementContextBackward_forward_ctx f backward
    forward_backward backward_forward hctx W)]

/-- Complete componentwise factor through an upper-pair normalization. -/
noncomputable def upperPairPullCartesianFactorGeomCore
    {U : AtomCarrier.{u}} {P : AATCorePackage U}
    (G : GeometryPackage.{u, v} U)
    (f : RefinementPackageHom ⟨P⟩ ⟨G.core⟩)
    (backward : SignedExactCoreReadingHom G.core P)
    (forward_backward : f.upper.comp backward =
      SignedExactCoreReadingHom.refl P)
    (backward_forward : backward.comp f.upper =
      SignedExactCoreReadingHom.refl G.core)
    (R : RealizationExactUpperEquivalence
      (refinementExactUpperEquivalence f backward
        forward_backward backward_forward))
    (hctx : ∀ V : G.site.category,
      (refinementGeometryContextForward
        (G := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
          G f.upper backward) (H := G) f
        (refinementGeometryContextBackward
          (G := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
            G f.upper backward) (H := G) f V)).ctx = V.ctx)
    {K : GeometryPackage.{u, v} U}
    (g : RefinementPackageHom ⟨K.core⟩ ⟨P⟩)
    (T : RefinementGeomReadHom K G (g.comp f)) :
    RefinementGeomReadHom K
      (UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
        G f.upper backward) g := by
  let e := refinementExactUpperEquivalence f backward
    forward_backward backward_forward
  exact {
    coverage := {
      requiredSupport := T.coverage.requiredSupport
      requiredEquationCoordinate := T.coverage.requiredEquationCoordinate
      selectedViolationWitness := T.coverage.selectedViolationWitness
      requiredAxis := T.coverage.requiredAxis
      supportVisibleOn := T.coverage.supportVisibleOn
      equationCoordinateVisibleOn := T.coverage.equationCoordinateVisibleOn
      violationWitnessVisibleOn := T.coverage.violationWitnessVisibleOn
      axisReadableOn := T.coverage.axisReadableOn
      boundaryVisibleOn := T.coverage.boundaryVisibleOn
    }
    overlap := {
      overlapIso := fun base left right => by
        let baseW := refinementGeometryContextForward f
          (⟨base⟩ : (UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
            G f.upper backward).site.category)
        let leftW := refinementGeometryContextForward f
          (⟨left⟩ : (UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
            G f.upper backward).site.category)
        let rightW := refinementGeometryContextForward f
          (⟨right⟩ : (UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
            G f.upper backward).site.category)
        let mapped := (refinementGeometryContextInverse
          (G := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
            G f.upper backward) (H := G) f).mapIso
          (T.overlap.overlapIso baseW.ctx leftW.ctx rightW.ctx)
        refine (eqToIso ?_).trans (mapped.trans (eqToIso ?_))
        · apply contextObjectExt
          dsimp [mapped, baseW, leftW, rightW]
          rw [refinementCompositeContextBackward_forward_ctx f backward
            forward_backward backward_forward hctx g
            (⟨base⟩ : (UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
              G f.upper backward).site.category)]
          rw [refinementCompositeContextBackward_forward_ctx f backward
            forward_backward backward_forward hctx g
            (⟨left⟩ : (UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
              G f.upper backward).site.category)]
          rw [refinementCompositeContextBackward_forward_ctx f backward
            forward_backward backward_forward hctx g
            (⟨right⟩ : (UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
              G f.upper backward).site.category)]
          symm
          exact refinementContextBackward_forward_ctx f backward
            forward_backward backward_forward hctx
              (refinementGeometryContextForward (G := K)
                (H := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
                  G f.upper backward) g
                ⟨K.geometry.overlap.overlap
                  (refinementGeometryContextBackwardMap g base)
                  (refinementGeometryContextBackwardMap g left)
                  (refinementGeometryContextBackwardMap g right)⟩)
        · apply contextObjectExt
          rfl
    }
    coefficientHom := T.coefficientHom
    raw_eq := by
      rw [UpperGeometryCleavage.pullGeometryPackageAlongUpperPair_raw]
      rw [T.raw_eq]
      change UpperGeometryCleavage.rawReindexUpper G.geometry
          (UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
            G f.upper backward).geometry backward
          (UpperGeometryCleavage.rawReindexUpper K.geometry G.geometry
            (g.upper.comp f.upper) (K.raw.baseChange T.coefficientHom)) =
        UpperGeometryCleavage.rawReindexUpper K.geometry
          (UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
            G f.upper backward).geometry g.upper
          (K.raw.baseChange T.coefficientHom)
      rw [← UpperGeometryCleavage.rawReindexUpper_comp K.geometry G.geometry
        (UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
          G f.upper backward).geometry]
      rw [signed_comp_assoc, forward_backward, signed_comp_refl]
    supportComp := fun W support =>
      R.supportInverseAtForward
        (refinementGeometryContextForward (G := K)
          (H := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
            G f.upper backward) g W)
        (T.supportComp W support)
    axisComp := fun W axis =>
      R.axisInverseAtForward
        (refinementGeometryContextForward (G := K)
          (H := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
            G f.upper backward) g W)
        (T.axisComp W axis)
    observableComp := fun W observable =>
      R.observableInverseAtForward
        (refinementGeometryContextForward (G := K)
          (H := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
            G f.upper backward) g W)
        (T.observableComp W observable)
    supportReads := by
      intro W support atom hs
      apply R.supportInverseAtForward_reads
        (refinementGeometryContextForward (G := K)
          (H := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
            G f.upper backward) g W) (T.supportComp W support)
        (g.upper.atomEquiv atom)
      simpa [RefinementPackageHom.comp, SignedExactCoreReadingHom.comp,
        EquationSystemExactTransport.comp] using T.supportReads W support atom hs
    axisReads := by
      intro W axis ha
      apply R.axisInverseAtForward_reads
        (refinementGeometryContextForward (G := K)
          (H := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
            G f.upper backward) g W) (T.axisComp W axis)
      simpa [RefinementPackageHom.comp, SignedExactCoreReadingHom.comp,
        EquationSystemExactTransport.comp] using T.axisReads W axis ha
    observableReads := by
      intro W observable ho
      apply R.observableInverseAtForward_reads
        (refinementGeometryContextForward (G := K)
          (H := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
            G f.upper backward) g W) (T.observableComp W observable)
      simpa [RefinementPackageHom.comp, SignedExactCoreReadingHom.comp,
        EquationSystemExactTransport.comp] using T.observableReads W observable ho
    support_naturality := by
      intro W V w support
      calc
        _ = R.supportInverseAtForward
            (refinementGeometryContextForward (G := K)
              (H := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
                G f.upper backward) g V)
            ((G.core.contextPreorder.morphism
              (leOfHom ((upperCoreContextFunctor f.upper).map
                ((refinementGeometryContextFunctor (G := K)
                  (H := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
                    G f.upper backward) g).map w)))).supportMap
              (T.supportComp W support)) :=
          R.supportInverseAtForward_naturality
            ((refinementGeometryContextFunctor (G := K)
              (H := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
                G f.upper backward) g).map w) (T.supportComp W support)
        _ = _ := congrArg (R.supportInverseAtForward
            (refinementGeometryContextForward (G := K)
              (H := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
                G f.upper backward) g V))
          (T.support_naturality w support)
    axis_naturality := by
      intro W V w axis
      calc
        _ = R.axisInverseAtForward
            (refinementGeometryContextForward (G := K)
              (H := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
                G f.upper backward) g V)
            ((G.core.contextPreorder.morphism
              (leOfHom ((upperCoreContextFunctor f.upper).map
                ((refinementGeometryContextFunctor (G := K)
                  (H := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
                    G f.upper backward) g).map w)))).axisMap
              (T.axisComp W axis)) :=
          R.axisInverseAtForward_naturality
            ((refinementGeometryContextFunctor (G := K)
              (H := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
                G f.upper backward) g).map w) (T.axisComp W axis)
        _ = _ := congrArg (R.axisInverseAtForward
            (refinementGeometryContextForward (G := K)
              (H := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
                G f.upper backward) g V))
          (T.axis_naturality w axis)
    observable_naturality := by
      intro W V w observable
      calc
        _ = R.observableInverseAtForward
            (refinementGeometryContextForward (G := K)
              (H := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
                G f.upper backward) g W)
            ((G.core.contextPreorder.morphism
              (leOfHom ((upperCoreContextFunctor f.upper).map
                ((refinementGeometryContextFunctor (G := K)
                  (H := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
                    G f.upper backward) g).map w)))).observableRestrict
              (T.observableComp V observable)) :=
          R.observableInverseAtForward_naturality
            ((refinementGeometryContextFunctor (G := K)
              (H := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
                G f.upper backward) g).map w) (T.observableComp V observable)
        _ = _ := congrArg (R.observableInverseAtForward
            (refinementGeometryContextForward (G := K)
              (H := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
                G f.upper backward) g W))
          (T.observable_naturality w observable)
  }

namespace UpperGeometryCompatibleProblemInputData

/-- Premise-free finite base-route specialization of the complete universal
factor geometry contract. -/
noncomputable def canonicalAuthoredBaseRouteCartesianFactorGeomCoreAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (i : P.Vertex) {K : GeometryPackage.{u, v} U}
    (g : RefinementPackageHom ⟨K.core⟩
      ⟨(input.canonicalAuthoredBaseRouteGeometryAt i).core⟩)
    (T : RefinementGeomReadHom K (input.sourceGeometry i).package
      (g.comp (input.generatedBaseRouteLegAt i).base)) :
    RefinementGeomReadHom K (input.canonicalAuthoredBaseRouteGeometryAt i) g :=
  upperPairPullCartesianFactorGeomCore
    (input.sourceGeometry i).package
    (input.generatedBaseRouteLegAt i).base
    (input.generatedBaseRouteUpperEquivalenceAt i).backward
    (input.generatedBaseRouteUpperEquivalenceAt i).forward_backward
    (input.generatedBaseRouteUpperEquivalenceAt i).backward_forward
    (by
      simpa only [refinementExactUpperEquivalence] using
        input.generatedBaseRouteRealizationExactAt i)
    (input.canonicalAuthoredBaseRouteContextForward_backwardAt i) g T

/-- Premise-free finite pulled-route specialization of the complete universal
factor geometry contract. -/
noncomputable def canonicalAuthoredPulledRouteCartesianFactorGeomCoreAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (i : P.Vertex) {K : GeometryPackage.{u, v} U}
    (g : RefinementPackageHom ⟨K.core⟩
      ⟨(input.canonicalAuthoredPulledRouteGeometryAt i).core⟩)
    (T : RefinementGeomReadHom K (input.sourceGeometry i).package
      (g.comp (input.generatedPulledRouteLegAt i).base)) :
    RefinementGeomReadHom K (input.canonicalAuthoredPulledRouteGeometryAt i) g :=
  upperPairPullCartesianFactorGeomCore
    (input.sourceGeometry i).package
    (input.generatedPulledRouteLegAt i).base
    (input.generatedPulledRouteUpperEquivalenceAt i).backward
    (input.generatedPulledRouteUpperEquivalenceAt i).forward_backward
    (input.generatedPulledRouteUpperEquivalenceAt i).backward_forward
    (by
      simpa only [refinementExactUpperEquivalence] using
        input.generatedPulledRouteRealizationExactAt i)
    (input.canonicalAuthoredPulledRouteContextForward_backwardAt i) g T

end UpperGeometryCompatibleProblemInputData

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct

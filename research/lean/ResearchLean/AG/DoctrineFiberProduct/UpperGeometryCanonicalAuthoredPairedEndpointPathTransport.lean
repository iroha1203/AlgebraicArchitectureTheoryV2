import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCanonicalAuthoredFullPairedReselection

/-!
# Endpoint and path-leg transport for canonical-authored full pairs

This module transports the first two conjuncts of the native
canonical-authored paired relation across the actual solution and reselection
equivalences.  The path-leg proofs transport the supplied triangles
fieldwise; they do not regenerate a destination triangle from endpoint
intertwining.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 6000000

/-- An intertwining square is invariant under simultaneous endpoint
conjugation. -/
theorem conjugatedIntertwining
    {C : Type u} [Category.{v} C] {X Y X' Y' : C}
    (sourceIso : X ≅ X') (targetIso : Y ≅ Y')
    (sourceAut : X ⟶ X) (hom : X ⟶ Y) (targetAut : Y ⟶ Y)
    (intertwining : sourceAut ≫ hom = hom ≫ targetAut) :
    ((sourceIso.inv ≫ sourceAut) ≫ sourceIso.hom) ≫
        ((sourceIso.inv ≫ hom) ≫ targetIso.hom) =
      ((sourceIso.inv ≫ hom) ≫ targetIso.hom) ≫
        ((targetIso.inv ≫ targetAut) ≫ targetIso.hom) := by
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
    congrArg (fun middle => sourceIso.inv ≫ middle ≫ targetIso.hom)
      intertwining

namespace UpperGeometryCompatibleProblemInputData

/-- Canonical-authored endpoint intertwining is carried forward by the exact
solution and reselection conjugations. -/
theorem canonicalAuthoredEndpointIntertwining_forward_transport
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {solution : CanonicalUpperRefinementBCSolution input}
    {base : CanonicalAuthoredBaseCoefficientTrivialUpperEdgeReselection input}
    {pulled :
      CanonicalAuthoredPulledCoefficientTrivialUpperEdgeReselection input}
    (endpoint :
      CanonicalAuthoredCoefficientTrivialUpperReselectionEndpointIntertwining
        solution base pulled) :
    CoefficientTrivialUpperReselectionEndpointIntertwining
      (input.canonicalSolutionForward solution)
      (input.canonicalAuthoredBaseCoefficientTrivialReselectionForward base)
      (input.canonicalAuthoredPulledCoefficientTrivialReselectionForward
        pulled) := by
  intro i j edge
  change
    (CompositeFiberAut.hom
      (input.canonicalAuthoredBaseCompositeFiberAutForwardAt j
        (base.toUpperEdgeReselection i j edge))).comp
        (input.canonicalSolutionForwardAt solution j) =
      (input.canonicalSolutionForwardAt solution j).comp
        (CompositeFiberAut.hom
          (input.canonicalAuthoredPulledCompositeFiberAutForwardAt j
            (pulled.toUpperEdgeReselection i j edge)))
  rw [input.canonicalAuthoredBaseCompositeFiberAutForwardAt_hom,
    input.canonicalAuthoredPulledCompositeFiberAutForwardAt_hom,
    input.canonicalSolutionForwardAt_exact_normalization]
  exact conjugatedIntertwining
    (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt j)
    (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt j)
    _ _ _ (endpoint edge)

/-- Generated endpoint intertwining is returned to the canonical-authored
routes by the inverse exact conjugations. -/
theorem canonicalAuthoredEndpointIntertwining_backward_transport
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {solution : GeometryCompatibleUpperRefinementBCSolution input}
    {base : GeneratedBaseCoefficientTrivialUpperEdgeReselection input}
    {pulled : GeneratedPulledCoefficientTrivialUpperEdgeReselection input}
    (endpoint : CoefficientTrivialUpperReselectionEndpointIntertwining
      solution base pulled) :
    CanonicalAuthoredCoefficientTrivialUpperReselectionEndpointIntertwining
      (input.generatedSolutionBackward solution)
      (input.canonicalAuthoredBaseCoefficientTrivialReselectionBackward base)
      (input.canonicalAuthoredPulledCoefficientTrivialReselectionBackward
        pulled) := by
  intro i j edge
  change
    (CompositeFiberAut.hom
      (input.canonicalAuthoredBaseCompositeFiberAutBackwardAt j
        (base.toUpperEdgeReselection i j edge))).comp
        (input.generatedSolutionBackwardAt solution j) =
      (input.generatedSolutionBackwardAt solution j).comp
        (CompositeFiberAut.hom
          (input.canonicalAuthoredPulledCompositeFiberAutBackwardAt j
            (pulled.toUpperEdgeReselection i j edge)))
  rw [input.canonicalAuthoredBaseCompositeFiberAutBackwardAt_hom,
    input.canonicalAuthoredPulledCompositeFiberAutBackwardAt_hom,
    input.generatedSolutionBackwardAt_exact_normalization]
  exact conjugatedIntertwining
    (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt j).symm
    (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt j).symm
    _ _ _ (endpoint edge)

/-- The supplied canonical-authored path-leg triangle is carried to the
generated routes. -/
theorem canonicalAuthoredReselectedPathLegTriangle_forward_transport
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {solution : CanonicalUpperRefinementBCSolution input}
    {base : CanonicalAuthoredBaseCoefficientTrivialUpperEdgeReselection input}
    {pulled :
      CanonicalAuthoredPulledCoefficientTrivialUpperEdgeReselection input}
    (pathTriangle :
      CanonicalAuthoredReselectedPathLegTriangle solution base pulled) :
    ReselectedPathLegTriangle (input.canonicalSolutionForward solution)
      (input.canonicalAuthoredBaseCoefficientTrivialReselectionForward base)
      (input.canonicalAuthoredPulledCoefficientTrivialReselectionForward
        pulled) := by
  intro i j path
  change
    ((exactGeometryToRefinementGeometry U).map
      (upperReselectedPathLift input.generatedBaseRouteLiftData
        (input.canonicalAuthoredBaseCoefficientTrivialReselectionForward base).toUpperEdgeReselection
          path)) ≫
        input.generatedBaseRouteLegAt j =
      ((exactGeometryToRefinementGeometry U).map
        (input.canonicalSolutionForwardAt solution i)) ≫
        (((exactGeometryToRefinementGeometry U).map
          (upperReselectedPathLift input.generatedPulledRouteLiftData
            (input.canonicalAuthoredPulledCoefficientTrivialReselectionForward
              pulled).toUpperEdgeReselection path)) ≫
            input.generatedPulledRouteLegAt j)
  have baseBackward := congrArg
    (fun hom => (exactGeometryToRefinementGeometry U).map hom)
    (input.canonicalAuthoredBaseReselectedPath_backward_naturality
      (input.canonicalAuthoredBaseCoefficientTrivialReselectionForward base)
      path)
  change
    (exactGeometryToRefinementGeometry U).map
        (upperReselectedPathLift input.generatedBaseRouteLiftData
          (input.canonicalAuthoredBaseCoefficientTrivialReselectionForward base).toUpperEdgeReselection
            path ≫
              input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt j) =
      (exactGeometryToRefinementGeometry U).map
        (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt i ≫
          (upperReselectedPathLift input.canonicalAuthoredBaseRouteLiftData
            ((input.canonicalAuthoredBaseCoefficientTrivialReselectionBackward
              (input.canonicalAuthoredBaseCoefficientTrivialReselectionForward
                base)).toUpperEdgeReselection) path)) at baseBackward
  have baseBackward' :
      ((exactGeometryToRefinementGeometry U).map
        (upperReselectedPathLift input.generatedBaseRouteLiftData
          (input.canonicalAuthoredBaseCoefficientTrivialReselectionForward
            base).toUpperEdgeReselection path)) ≫
          (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt j).inv =
        (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).inv ≫
          ((exactGeometryToRefinementGeometry U).map
            (upperReselectedPathLift input.canonicalAuthoredBaseRouteLiftData
              base.toUpperEdgeReselection path)) := by
    rw [Functor.map_comp, Functor.map_comp,
      input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt_toRefinement i,
      input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt_toRefinement j,
      input.canonicalAuthoredBaseCoefficientTrivialReselectionBackward_forward]
      at baseBackward
    exact baseBackward
  have pulledForward := congrArg
    (fun hom => (exactGeometryToRefinementGeometry U).map hom)
    (input.canonicalAuthoredPulledReselectedPath_forward_naturality pulled path)
  change
    (exactGeometryToRefinementGeometry U).map
        (upperReselectedPathLift input.canonicalAuthoredPulledRouteLiftData
          pulled.toUpperEdgeReselection path ≫
            input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt j) =
      (exactGeometryToRefinementGeometry U).map
        (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt i ≫
          (upperReselectedPathLift input.generatedPulledRouteLiftData
            (input.canonicalAuthoredPulledCoefficientTrivialReselectionForward
              pulled).toUpperEdgeReselection path)) at pulledForward
  have pulledForward' :
      ((exactGeometryToRefinementGeometry U).map
        (upperReselectedPathLift input.canonicalAuthoredPulledRouteLiftData
          pulled.toUpperEdgeReselection path)) ≫
          (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt j).hom =
        (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).hom ≫
          ((exactGeometryToRefinementGeometry U).map
            (upperReselectedPathLift input.generatedPulledRouteLiftData
              (input.canonicalAuthoredPulledCoefficientTrivialReselectionForward
                pulled).toUpperEdgeReselection path)) := by
    rw [Functor.map_comp, Functor.map_comp,
      input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt_toRefinement i,
      input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt_toRefinement j]
      at pulledForward
    exact pulledForward
  rw [input.canonicalSolutionForwardAt_toRefinement]
  unfold canonicalSolutionForwardRefinementAt
  calc
    _ = ((exactGeometryToRefinementGeometry U).map
          (upperReselectedPathLift input.generatedBaseRouteLiftData
            (input.canonicalAuthoredBaseCoefficientTrivialReselectionForward
              base).toUpperEdgeReselection path)) ≫
        ((input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt j).inv ≫
          input.canonicalAuthoredBaseRouteGeometryHomAt j) := by
      rw [input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_inv_fac]
    _ = (((exactGeometryToRefinementGeometry U).map
          (upperReselectedPathLift input.generatedBaseRouteLiftData
            (input.canonicalAuthoredBaseCoefficientTrivialReselectionForward
              base).toUpperEdgeReselection path)) ≫
        (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt j).inv) ≫
          input.canonicalAuthoredBaseRouteGeometryHomAt j := by
      simp only [Category.assoc]
    _ = (((input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).inv ≫
          (exactGeometryToRefinementGeometry U).map
            (upperReselectedPathLift input.canonicalAuthoredBaseRouteLiftData
              base.toUpperEdgeReselection path))) ≫
          input.canonicalAuthoredBaseRouteGeometryHomAt j := by
      rw [baseBackward']
    _ = (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).inv ≫
        (((exactGeometryToRefinementGeometry U).map
          (upperReselectedPathLift input.canonicalAuthoredBaseRouteLiftData
            base.toUpperEdgeReselection path)) ≫
              input.canonicalAuthoredBaseRouteGeometryHomAt j) := by
      simp only [Category.assoc]
    _ = (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).inv ≫
        (((exactGeometryToRefinementGeometry U).map (solution.component i)) ≫
          (((exactGeometryToRefinementGeometry U).map
            (upperReselectedPathLift
              input.canonicalAuthoredPulledRouteLiftData
              pulled.toUpperEdgeReselection path)) ≫
                input.canonicalAuthoredPulledRouteGeometryHomAt j)) := by
      simpa only [Category.assoc] using
        congrArg
          (fun hom =>
            (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).inv ≫
              hom)
          (pathTriangle path)
    _ = (((input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).inv ≫
          (exactGeometryToRefinementGeometry U).map (solution.component i)) ≫
            (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).hom) ≫
        (((exactGeometryToRefinementGeometry U).map
          (upperReselectedPathLift input.generatedPulledRouteLiftData
            (input.canonicalAuthoredPulledCoefficientTrivialReselectionForward
              pulled).toUpperEdgeReselection path)) ≫
              input.generatedPulledRouteLegAt j) := by
      rw [← input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_hom_fac j]
      simp only [Category.assoc]
      simpa only [Category.assoc] using
        congrArg
          (fun hom =>
            ((input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).inv ≫
              (exactGeometryToRefinementGeometry U).map (solution.component i)) ≫
                hom ≫ input.generatedPulledRouteLegAt j)
          pulledForward'

/-- The supplied generated path-leg triangle is returned to the independently
authored routes. -/
theorem canonicalAuthoredReselectedPathLegTriangle_backward_transport
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {solution : GeometryCompatibleUpperRefinementBCSolution input}
    {base : GeneratedBaseCoefficientTrivialUpperEdgeReselection input}
    {pulled : GeneratedPulledCoefficientTrivialUpperEdgeReselection input}
    (pathTriangle : ReselectedPathLegTriangle solution base pulled) :
    CanonicalAuthoredReselectedPathLegTriangle
      (input.generatedSolutionBackward solution)
      (input.canonicalAuthoredBaseCoefficientTrivialReselectionBackward base)
      (input.canonicalAuthoredPulledCoefficientTrivialReselectionBackward
        pulled) := by
  intro i j path
  change
    ((exactGeometryToRefinementGeometry U).map
      (upperReselectedPathLift input.canonicalAuthoredBaseRouteLiftData
        (input.canonicalAuthoredBaseCoefficientTrivialReselectionBackward base).toUpperEdgeReselection
          path)) ≫
        input.canonicalAuthoredBaseRouteGeometryHomAt j =
      ((exactGeometryToRefinementGeometry U).map
        (input.generatedSolutionBackwardAt solution i)) ≫
        (((exactGeometryToRefinementGeometry U).map
          (upperReselectedPathLift input.canonicalAuthoredPulledRouteLiftData
            (input.canonicalAuthoredPulledCoefficientTrivialReselectionBackward
              pulled).toUpperEdgeReselection path)) ≫
            input.canonicalAuthoredPulledRouteGeometryHomAt j)
  have baseForward := congrArg
    (fun hom => (exactGeometryToRefinementGeometry U).map hom)
    (input.canonicalAuthoredBaseReselectedPath_forward_naturality
      (input.canonicalAuthoredBaseCoefficientTrivialReselectionBackward base)
      path)
  change
    (exactGeometryToRefinementGeometry U).map
        (upperReselectedPathLift input.canonicalAuthoredBaseRouteLiftData
          (input.canonicalAuthoredBaseCoefficientTrivialReselectionBackward base).toUpperEdgeReselection
            path ≫
              input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt j) =
      (exactGeometryToRefinementGeometry U).map
        (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt i ≫
          (upperReselectedPathLift input.generatedBaseRouteLiftData
            ((input.canonicalAuthoredBaseCoefficientTrivialReselectionForward
              (input.canonicalAuthoredBaseCoefficientTrivialReselectionBackward
                base)).toUpperEdgeReselection) path)) at baseForward
  have baseForward' :
      ((exactGeometryToRefinementGeometry U).map
        (upperReselectedPathLift input.canonicalAuthoredBaseRouteLiftData
          (input.canonicalAuthoredBaseCoefficientTrivialReselectionBackward
            base).toUpperEdgeReselection path)) ≫
          (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt j).hom =
        (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom ≫
          ((exactGeometryToRefinementGeometry U).map
            (upperReselectedPathLift input.generatedBaseRouteLiftData
              base.toUpperEdgeReselection path)) := by
    rw [Functor.map_comp, Functor.map_comp,
      input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt_toRefinement i,
      input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt_toRefinement j,
      input.canonicalAuthoredBaseCoefficientTrivialReselectionForward_backward]
      at baseForward
    exact baseForward
  have pulledBackward := congrArg
    (fun hom => (exactGeometryToRefinementGeometry U).map hom)
    (input.canonicalAuthoredPulledReselectedPath_backward_naturality pulled path)
  change
    (exactGeometryToRefinementGeometry U).map
        (upperReselectedPathLift input.generatedPulledRouteLiftData
          pulled.toUpperEdgeReselection path ≫
            input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt j) =
      (exactGeometryToRefinementGeometry U).map
        (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt i ≫
          (upperReselectedPathLift input.canonicalAuthoredPulledRouteLiftData
            (input.canonicalAuthoredPulledCoefficientTrivialReselectionBackward
              pulled).toUpperEdgeReselection path)) at pulledBackward
  have pulledBackward' :
      ((exactGeometryToRefinementGeometry U).map
        (upperReselectedPathLift input.generatedPulledRouteLiftData
          pulled.toUpperEdgeReselection path)) ≫
          (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt j).inv =
        (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).inv ≫
          ((exactGeometryToRefinementGeometry U).map
            (upperReselectedPathLift input.canonicalAuthoredPulledRouteLiftData
              (input.canonicalAuthoredPulledCoefficientTrivialReselectionBackward
                pulled).toUpperEdgeReselection path)) := by
    rw [Functor.map_comp, Functor.map_comp,
      input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt_toRefinement i,
      input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt_toRefinement j]
      at pulledBackward
    exact pulledBackward
  rw [input.generatedSolutionBackwardAt_toRefinement]
  unfold generatedSolutionBackwardRefinementAt
  calc
    _ = ((exactGeometryToRefinementGeometry U).map
          (upperReselectedPathLift input.canonicalAuthoredBaseRouteLiftData
            (input.canonicalAuthoredBaseCoefficientTrivialReselectionBackward
              base).toUpperEdgeReselection path)) ≫
        ((input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt j).hom ≫
          input.generatedBaseRouteLegAt j) := by
      rw [input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_hom_fac]
    _ = (((exactGeometryToRefinementGeometry U).map
          (upperReselectedPathLift input.canonicalAuthoredBaseRouteLiftData
            (input.canonicalAuthoredBaseCoefficientTrivialReselectionBackward
              base).toUpperEdgeReselection path)) ≫
        (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt j).hom) ≫
          input.generatedBaseRouteLegAt j := by
      simp only [Category.assoc]
    _ = (((input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom ≫
          (exactGeometryToRefinementGeometry U).map
            (upperReselectedPathLift input.generatedBaseRouteLiftData
              base.toUpperEdgeReselection path))) ≫
          input.generatedBaseRouteLegAt j := by
      rw [baseForward']
    _ = (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom ≫
        (((exactGeometryToRefinementGeometry U).map
          (upperReselectedPathLift input.generatedBaseRouteLiftData
            base.toUpperEdgeReselection path)) ≫
              input.generatedBaseRouteLegAt j) := by
      simp only [Category.assoc]
    _ = (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom ≫
        (((exactGeometryToRefinementGeometry U).map (solution.component i)) ≫
          (((exactGeometryToRefinementGeometry U).map
            (upperReselectedPathLift input.generatedPulledRouteLiftData
              pulled.toUpperEdgeReselection path)) ≫
                input.generatedPulledRouteLegAt j)) := by
      simpa only [Category.assoc] using
        congrArg
          (fun hom =>
            (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom ≫
              hom)
          (pathTriangle path)
    _ = (((input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom ≫
          (exactGeometryToRefinementGeometry U).map (solution.component i)) ≫
            (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).inv) ≫
        (((exactGeometryToRefinementGeometry U).map
          (upperReselectedPathLift input.canonicalAuthoredPulledRouteLiftData
            (input.canonicalAuthoredPulledCoefficientTrivialReselectionBackward
              pulled).toUpperEdgeReselection path)) ≫
              input.canonicalAuthoredPulledRouteGeometryHomAt j) := by
      rw [← input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_inv_fac j]
      simp only [Category.assoc]
      simpa only [Category.assoc] using
        congrArg
          (fun hom =>
            ((input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom ≫
              (exactGeometryToRefinementGeometry U).map (solution.component i)) ≫
                hom ≫ input.canonicalAuthoredPulledRouteGeometryHomAt j)
          pulledBackward'

end UpperGeometryCompatibleProblemInputData

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct

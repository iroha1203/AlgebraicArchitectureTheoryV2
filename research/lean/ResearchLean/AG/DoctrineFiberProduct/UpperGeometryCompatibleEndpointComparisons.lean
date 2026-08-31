import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleAuthoredEndpoints
import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryMateComponents

/-!
# Endpoint-equivalence inputs for the compatible upper problem

The route realization equivalences and the core endpoint normalizations arise
from different constructions.  This module fixes both at each finite vertex,
without pretending that object-level upper-pair normalization itself supplies
Support, Axis, or Observable maps.  The declarations are the typed inputs for
the subsequent strong-cartesian endpoint comparison.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 3000000

namespace UpperGeometryCompatibleProblemInputData

/-- Exact upper equivalence carried by the generated base-first route at one
finite vertex. -/
noncomputable def generatedBaseRouteUpperEquivalenceAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) := by
  let localCtx := ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩)
  let target := input.sourceTargetGeometryAt i
  exact (UpperGeometryCleavage.exactInversePackageUpperEquivalence
      (UpperGeometryCleavage.baseRefinementGeometry localCtx target)
      (UpperGeometryCleavage.baseRouteExactArrow localCtx target)).comp
    (UpperGeometryCleavage.refinementInversePackageUpperEquivalence
      target.geometry
      (localCtx.configuration.baseRefinementAt localCtx.source)
      localCtx.condition target.packagePoint_eq)

/-- The theorem-generated realization-exact equivalence for the base-first
route at one finite vertex. -/
noncomputable def generatedBaseRouteRealizationExactAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    RealizationExactUpperEquivalence
      (input.generatedBaseRouteUpperEquivalenceAt i) :=
  UpperGeometryCleavage.baseRouteRealizationExact
    (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
    (input.sourceTargetGeometryAt i)

/-- The finite base-route equivalence has the literal generated route-leg
upper map. -/
theorem generatedBaseRouteUpperEquivalenceAt_forward_eq
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.generatedBaseRouteUpperEquivalenceAt i).forward =
      (input.generatedBaseRouteLegAt i).base.upper := by
  exact UpperGeometryCleavage.baseRouteRealizationExact_forward_eq
    (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
    (input.sourceTargetGeometryAt i)

/-- Exact upper equivalence carried by the generated pulled-first route at one
finite vertex. -/
noncomputable def generatedPulledRouteUpperEquivalenceAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) := by
  let localCtx := ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩)
  let target := input.sourceTargetGeometryAt i
  exact (UpperGeometryCleavage.refinementInversePackageUpperEquivalence
      (UpperGeometryCleavage.pullbackTargetGeometry localCtx target)
      (localCtx.configuration.pulledRefinementAt localCtx.source)
      (pulledRealizedReflection localCtx.configuration localCtx.source
        localCtx.condition)
      (UpperGeometryCleavage.pullbackTargetGeometry_packagePoint_eq
        localCtx target)).comp
    (UpperGeometryCleavage.exactInversePackageUpperEquivalence target.geometry
      (UpperGeometryCleavage.pullbackTargetExactArrow localCtx target))

/-- The theorem-generated realization-exact equivalence for the pulled-first
route at one finite vertex. -/
noncomputable def generatedPulledRouteRealizationExactAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    RealizationExactUpperEquivalence
      (input.generatedPulledRouteUpperEquivalenceAt i) :=
  UpperGeometryCleavage.pulledRouteRealizationExact
    (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
    (input.sourceTargetGeometryAt i)

/-- The finite pulled-route equivalence has the literal generated route-leg
upper map. -/
theorem generatedPulledRouteUpperEquivalenceAt_forward_eq
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.generatedPulledRouteUpperEquivalenceAt i).forward =
      (input.generatedPulledRouteLegAt i).base.upper := by
  exact UpperGeometryCleavage.pulledRouteRealizationExact_forward_eq
    (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
    (input.sourceTargetGeometryAt i)

/-- Exact upper equivalence underlying the base endpoint core normalization.
It records only the two upper maps of the theorem-generated core isomorphism;
realization data are deliberately not inferred from this structure. -/
noncomputable def generatedBaseEndpointUpperEquivalenceAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    ExactUpperEquivalence
      (input.generatedAuthoredBaseRouteGeometryAt i).core
      (input.generatedBaseRouteFixedGeometryAt i).package.core where
  forward := (input.generatedBaseRouteCoreIsoAt i).inv.1.upper
  backward := (input.generatedBaseRouteCoreIsoAt i).hom.1.upper
  forward_backward := input.generatedBaseRouteEndpointUpper_inv_hom i
  backward_forward := input.generatedBaseRouteEndpointUpper_hom_inv i

/-- Exact upper equivalence underlying the independently normalized pulled
endpoint. -/
noncomputable def generatedPulledEndpointUpperEquivalenceAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    ExactUpperEquivalence
      (input.generatedAuthoredPulledRouteGeometryAt i).core
      (input.generatedPulledRouteFixedGeometryAt i).package.core where
  forward := (input.generatedPulledRouteCoreIsoAt i).inv.1.upper
  backward := (input.generatedPulledRouteCoreIsoAt i).hom.1.upper
  forward_backward := input.generatedPulledRouteEndpointUpper_inv_hom i
  backward_forward := input.generatedPulledRouteEndpointUpper_hom_inv i

end UpperGeometryCompatibleProblemInputData

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct

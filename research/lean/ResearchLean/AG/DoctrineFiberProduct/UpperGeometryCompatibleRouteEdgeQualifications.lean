import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleMateNaturality
import ResearchLean.AG.DoctrineFiberProduct.PackageProjectionBeckChevalleyExactness

/-!
# Isomorphism and cocartesian qualifications for compatible route edges

The authored source diagram lies in one core fiber.  Its strongly
cocartesian core and geometry edges are therefore isomorphisms.  This module
transports that invertibility through the two generated Cartesian route
squares and derives the G-109 strong-cocartesian qualifications without a new
input certificate.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v u₁ u₂ v₁ v₂

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 3000000

/-- Retag a strongly cocartesian morphism along an independently supplied
base-lift equality. -/
theorem stronglyCocartesian_of_isHomLift_support
    {Base : Type u₁} {Total : Type u₂}
    [Category.{v₁} Base] [Category.{v₂} Total]
    (projection : Total ⥤ Base) {source target : Base}
    {domain codomain : Total} (base : source ⟶ target)
    (hom : domain ⟶ codomain)
    [projection.IsStronglyCocartesian (projection.map hom) hom]
    [projection.IsHomLift base hom] :
    projection.IsStronglyCocartesian base hom := by
  subst_hom_lift projection base hom
  infer_instance

namespace UpperGeometryCompatibleProblemInputData

/-- Every source core-fiber diagram edge is an isomorphism because its
underlying edge is strongly cocartesian over the identity of the fiber. -/
theorem sourceFiberDiagramEdge_isIso
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    IsIso (input.sourceFiberDiagram.map (presentedEdgePath edge)) := by
  let sourceMap := input.sourceFiberDiagram.map (presentedEdgePath edge)
  letI : (packageProjection U).IsHomLift
      (𝟙 (ctx.configuration.targetPointAt ctx.source)) sourceMap.1 := sourceMap.2
  letI : (packageProjection U).IsStronglyCocartesian
      ((packageProjection U).map sourceMap.1) sourceMap.1 := by
    rw [← input.sourceTransport.edge_base edge]
    exact input.sourceTransport.edgeCoreStrong edge
  letI : (packageProjection U).IsStronglyCocartesian
      (𝟙 (ctx.configuration.targetPointAt ctx.source)) sourceMap.1 :=
    stronglyCocartesian_of_isHomLift_support
      (packageProjection U)
      (𝟙 (ctx.configuration.targetPointAt ctx.source)) sourceMap.1
  letI : IsIso sourceMap.1 := by
    exact CategoryTheory.Functor.IsStronglyCocartesian.isIso_of_base_isIso
      (p := packageProjection U)
      (f := 𝟙 (ctx.configuration.targetPointAt ctx.source)) sourceMap.1
  exact coreFiberHom_isIso_of_total_isIso sourceMap

/-- The underlying authored source core edge is an isomorphism. -/
theorem sourceTransportCoreEdge_isIso
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    IsIso (show (input.sourceGeometry i).package.core ⟶
      (input.sourceGeometry j).package.core from
        (input.sourceTransport.edgeLift edge).base) := by
  letI : IsIso (input.sourceFiberDiagram.map (presentedEdgePath edge)) :=
    input.sourceFiberDiagramEdge_isIso edge
  rw [input.sourceTransport.edge_base edge]
  change IsIso ((CategoryTheory.Functor.Fiber.fiberInclusion).map
    (input.sourceFiberDiagram.map (presentedEdgePath edge)))
  infer_instance

/-- Every authored source geometry edge is an isomorphism at the second
transport layer as well. -/
theorem sourceTransportGeometryEdge_isIso
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    IsIso (show (input.sourceGeometry i).package ⟶
      (input.sourceGeometry j).package from
        input.sourceTransport.edgeLift edge) := by
  let sourceEdge : (input.sourceGeometry i).package ⟶
      (input.sourceGeometry j).package :=
    input.sourceTransport.edgeLift edge
  change IsIso sourceEdge
  letI : IsIso ((geometryProjection U).map sourceEdge) :=
    input.sourceTransportCoreEdge_isIso edge
  letI : (geometryProjection U).IsStronglyCocartesian
      ((geometryProjection U).map sourceEdge) sourceEdge :=
    input.sourceTransport.edgeGeometryStrong edge
  exact CategoryTheory.Functor.IsStronglyCocartesian.isIso_of_base_isIso
    (p := geometryProjection U)
    (f := (geometryProjection U).map sourceEdge) sourceEdge

/-- Every generated base-route core edge is an isomorphism. -/
theorem generatedBaseRouteCoreEdge_isIso
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    IsIso (input.generatedBaseRouteCoreDiagram.map
      (presentedEdgePath edge)).1 := by
  letI : IsIso (input.sourceFiberDiagram.map (presentedEdgePath edge)) :=
    input.sourceFiberDiagramEdge_isIso edge
  letI : IsIso (input.generatedBaseRouteCoreDiagram.map
      (presentedEdgePath edge)) := by
    dsimp [generatedBaseRouteCoreDiagram,
      ActiveRefinementBCContext.baseCoreDiagram]
    infer_instance
  change IsIso ((CategoryTheory.Functor.Fiber.fiberInclusion).map
    (input.generatedBaseRouteCoreDiagram.map (presentedEdgePath edge)))
  infer_instance

/-- Every generated pulled-route core edge is an isomorphism. -/
theorem generatedPulledRouteCoreEdge_isIso
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    IsIso (input.generatedPulledRouteCoreDiagram.map
      (presentedEdgePath edge)).1 := by
  letI : IsIso (input.sourceFiberDiagram.map (presentedEdgePath edge)) :=
    input.sourceFiberDiagramEdge_isIso edge
  letI : IsIso (input.generatedPulledRouteCoreDiagram.map
      (presentedEdgePath edge)) := by
    dsimp [generatedPulledRouteCoreDiagram,
      ActiveRefinementBCContext.pulledCoreDiagram]
    infer_instance
  change IsIso ((CategoryTheory.Functor.Fiber.fiberInclusion).map
    (input.generatedPulledRouteCoreDiagram.map (presentedEdgePath edge)))
  infer_instance

/-- The exact core projection of every generated base-route geometry edge is
strongly cocartesian, derived from its generated isomorphism. -/
theorem generatedBaseRouteCoreEdge_isStronglyCocartesian
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (packageProjection U).IsStronglyCocartesian
      (input.generatedBaseRouteGeometryEdge edge).base.base
      (input.generatedBaseRouteGeometryEdge edge).base := by
  letI : IsIso (show (input.generatedBaseRouteGeometryAt i).core ⟶
      (input.generatedBaseRouteGeometryAt j).core from
        (input.generatedBaseRouteGeometryEdge edge).base) := by
    rw [input.generatedBaseRouteGeometryEdge_base]
    exact input.generatedBaseRouteCoreEdge_isIso edge
  letI : (packageProjection U).IsHomLift
      (input.generatedBaseRouteGeometryEdge edge).base.base
      (input.generatedBaseRouteGeometryEdge edge).base := by
    change (packageProjection U).IsHomLift
      ((packageProjection U).map
        (input.generatedBaseRouteGeometryEdge edge).base)
      (input.generatedBaseRouteGeometryEdge edge).base
    infer_instance
  exact CategoryTheory.Functor.IsStronglyCocartesian.of_isIso
    (p := packageProjection U)
    (f := (input.generatedBaseRouteGeometryEdge edge).base.base)
    (input.generatedBaseRouteGeometryEdge edge).base

/-- The exact core projection of every generated pulled-route geometry edge is
strongly cocartesian, derived from its generated isomorphism. -/
theorem generatedPulledRouteCoreEdge_isStronglyCocartesian
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (packageProjection U).IsStronglyCocartesian
      (input.generatedPulledRouteGeometryEdge edge).base.base
      (input.generatedPulledRouteGeometryEdge edge).base := by
  letI : IsIso (show (input.generatedPulledRouteGeometryAt i).core ⟶
      (input.generatedPulledRouteGeometryAt j).core from
        (input.generatedPulledRouteGeometryEdge edge).base) := by
    rw [input.generatedPulledRouteGeometryEdge_base]
    exact input.generatedPulledRouteCoreEdge_isIso edge
  letI : (packageProjection U).IsHomLift
      (input.generatedPulledRouteGeometryEdge edge).base.base
      (input.generatedPulledRouteGeometryEdge edge).base := by
    change (packageProjection U).IsHomLift
      ((packageProjection U).map
        (input.generatedPulledRouteGeometryEdge edge).base)
      (input.generatedPulledRouteGeometryEdge edge).base
    infer_instance
  exact CategoryTheory.Functor.IsStronglyCocartesian.of_isIso
    (p := packageProjection U)
    (f := (input.generatedPulledRouteGeometryEdge edge).base.base)
    (input.generatedPulledRouteGeometryEdge edge).base

end UpperGeometryCompatibleProblemInputData

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
